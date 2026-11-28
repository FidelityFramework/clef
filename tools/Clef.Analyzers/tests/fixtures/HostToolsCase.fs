// Negative control, exact reason: CLF002 refuses Zone A calls into the
// in-assembly host process wrapper Clef.Compiler.Utilities.HostTools (wiki §3.3).
namespace Clef.Compiler.Utilities

module HostTools =
    let runSolver (args : string) : int = args.Length

namespace ClefAnalyzerHostToolsCase

module Caller =
    let invokeSolver (args : string) : int =
        Clef.Compiler.Utilities.HostTools.runSolver args
