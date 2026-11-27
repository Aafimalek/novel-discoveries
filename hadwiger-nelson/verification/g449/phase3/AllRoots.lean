import SlimG449Data

namespace G449OrbitArithmetic

set_option maxRecDepth 32768
set_option maxHeartbeats 160000000

theorem roots_checked_math :
    roots.all (fun r => testNorm powers (dirs r)) = true := by decide +kernel

#print axioms roots_checked_math
end G449OrbitArithmetic
