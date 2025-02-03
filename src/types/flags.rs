/// API for object properties.
pub trait FlagIF {
    type FlagType;
    /// return true if the flag in on.
    fn is(&self, flag: Self::FlagType) -> bool;
    /// set the flag.
    fn set(&mut self, f: Self::FlagType, b: bool);
    // toggle the flag.
    fn toggle(&mut self, flag: Self::FlagType);
    /// toggle the flag off.
    fn turn_off(&mut self, flag: Self::FlagType);
    /// toggle the flag on.
    fn turn_on(&mut self, flag: Self::FlagType);
}

bitflags! {
    /// Misc flags used by [`Clause`](`crate::cdb::Clause`).
    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct FlagClause: u8 {
        /// a clause is a generated clause by conflict analysis and is removable.
        const LEARNT       = 0b0000_0001;
        /// used in conflict analyze
        const USED         = 0b0000_0010;
        /// a clause or var is enqueued for eliminator.
        const ENQUEUED     = 0b0000_0100;
        /// a clause is registered in vars' occurrence list.
        const OCCUR_LINKED = 0b0000_1000;
        /// a given clause derived a learnt which LBD is smaller than 20.
        const DERIVE20     = 0b0001_0000;
    }
}

bitflags! {
    /// Misc flags used by [`Var`](`crate::assign::Var`).
    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct FlagVar: u8 {
        /// * the previous assigned value of a Var.
        const PHASE        = 0b0000_0001;
        /// used in conflict analyze
        const USED         = 0b0000_0010;
        /// a var is eliminated and managed by eliminator.
        const ELIMINATED   = 0b0000_0100;
        /// a clause or var is enqueued for eliminator.
        const ENQUEUED     = 0b0000_1000;
        /// a var is checked during in the current conflict analysis.
        const CA_SEEN      = 0b0001_0000;

        #[cfg(feature = "debug_propagation")]
        /// check propagation
        const PROPAGATED   = 0b0010_0000;
    }
}
