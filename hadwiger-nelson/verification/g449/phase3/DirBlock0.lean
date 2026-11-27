import SlimG449Data

namespace G449OrbitArithmetic

set_option maxRecDepth 32768
set_option maxHeartbeats 160000000

theorem dir_block_0 :
    (List.range 7).all (fun j => testNorm powers (dirs (0+j))) = true := by decide +kernel

#print axioms dir_block_0
end G449OrbitArithmetic
