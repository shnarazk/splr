//! Module `restart` provides restart heuristics.
use crate::types::*;

/// API for [`restart`](`crate::solver::RestartIF::restart`)
pub trait RestartIF: Instantiate {
    /// check blocking and forcing restart condition.
    fn restart(&mut self, ldb: &EmaView, ent: &EmaView) -> bool;
    /// set stabilization parameters
    fn set_stage_parameters(&mut self, step: usize);
    /// adjust restart threshold
    fn set_segment_parameters(&mut self, segment_scale: usize);
    /// Compute the dynamic LBD trend threshold for micro restarts.
    ///
    /// When `e_mode_adaptive_restart` is enabled, the threshold adapts based on
    /// the exploration/exploitation balance (`e_mode`):
    /// - Deep backjumps (high `e_mode` trend) → raise threshold → restart less often,
    ///   because deep backjumps already provide restart-like diversification.
    /// - Shallow backjumps (low `e_mode` trend) → lower threshold → restart more often,
    ///   because the solver needs restarts for diversification.
    fn lbd_restart_threshold(&self, e_mode: &EmaView) -> f64;
}

const FUEL: f64 = 2.0;
const SCALE: f64 = 64.0;

/// Base LBD trend threshold (matches the previous hardcoded value of 2.0).
const LBD_THRESHOLD_BASE: f64 = 2.0;
/// Minimum LBD trend threshold — prevents restarting too aggressively.
const LBD_THRESHOLD_MIN: f64 = 1.2;
/// Maximum LBD trend threshold — prevents suppressing restarts entirely.
const LBD_THRESHOLD_MAX: f64 = 4.0;
/// Sensitivity of the threshold to `e_mode` trend deviation from 1.0.
///
/// With the default value of 1.0 and typical `e_mode` trend fluctuations of ±0.3:
/// - trend 0.7 → threshold ≈ 1.7 (restart sooner)
/// - trend 1.0 → threshold = 2.0 (unchanged)
/// - trend 1.3 → threshold ≈ 2.3 (restart later)
const E_MODE_SENSITIVITY: f64 = 1.0;

/// `RestartManager` provides restart API and holds data about restart conditions.
#[derive(Clone, Debug, Default)]
pub struct RestartManager {
    penetration_energy: f64,
    pub penetration_energy_charged: f64,
    penetration_energy_unit: f64,
    field_scale: f64,
    /// Base LBD trend threshold for micro restarts.
    lbd_threshold_base: f64,
    /// Minimum allowed LBD trend threshold.
    lbd_threshold_min: f64,
    /// Maximum allowed LBD trend threshold.
    lbd_threshold_max: f64,
    /// How strongly `e_mode` trend influences the threshold.
    e_mode_sensitivity: f64,
}

impl Instantiate for RestartManager {
    fn instantiate(_config: &Config, _cnf: &CNFDescription) -> Self {
        RestartManager {
            penetration_energy: FUEL,
            penetration_energy_charged: FUEL,
            penetration_energy_unit: FUEL,
            field_scale: 1.0 / SCALE,
            lbd_threshold_base: LBD_THRESHOLD_BASE,
            lbd_threshold_min: LBD_THRESHOLD_MIN,
            lbd_threshold_max: LBD_THRESHOLD_MAX,
            e_mode_sensitivity: E_MODE_SENSITIVITY,
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        if e == SolverEvent::Restart {
            self.penetration_energy = self.penetration_energy_charged;
        }
    }
}

impl RestartIF for RestartManager {
    fn restart(&mut self, lbd: &EmaView, ent: &EmaView) -> bool {
        let gscale = |x: f64| self.field_scale * (x - 1.0) + 1.0;
        self.penetration_energy -= (lbd.trend() + gscale(ent.trend())) - 2.0;
        self.penetration_energy < 0.0
    }
    fn set_segment_parameters(&mut self, segment_scale: usize) {
        let factor = 0.5 * (segment_scale.trailing_zeros() + 1) as f64;
        self.field_scale = 1.0 / (SCALE - factor);
        self.penetration_energy_unit *= 10.0_f64.powf(-0.1);
    }
    fn set_stage_parameters(&mut self, stage_scale: usize) {
        let e = self.penetration_energy_unit * (stage_scale as f64);
        self.penetration_energy_charged = e;
        self.penetration_energy = e;
    }
    fn lbd_restart_threshold(&self, e_mode: &EmaView) -> f64 {
        if cfg!(feature = "e_mode_adaptive_restart") {
            // e_mode.trend() = fast / slow, centered around 1.0.
            //   > 1.0 ⇒ recent backjumps deeper than long-term average (exploration)
            //   < 1.0 ⇒ recent backjumps shallower than average (exploitation)
            //
            // Linear adjustment:
            //   threshold = base + sensitivity * (trend - 1.0)
            //
            // Clamped to [min, max] to keep the solver well-behaved.
            let trend = e_mode.trend();
            let adjustment = self.e_mode_sensitivity * (trend - 1.0);
            (self.lbd_threshold_base + adjustment)
                .clamp(self.lbd_threshold_min, self.lbd_threshold_max)
        } else {
            self.lbd_threshold_base
        }
    }
}
