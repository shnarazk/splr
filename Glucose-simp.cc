#include <errno.h>
#include <signal.h>
#include <zlib.h>
#include <sys/resource.h>
#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "simp/SimpSolver.h"

using namespace Glucose;
static Solver* solver;

int main(int argc, char** argv)
{
#if defined(__linux__)
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", true);
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
        parseOptions(argc, argv, true);
        SimpSolver  S;
        S.use_simplification = pre;
        gzclose(in);
        S.parsing = 0;
	S.eliminate(true);
        vec<Lit> dummy;
        lbool ret = S.solveLimited(dummy);
}
