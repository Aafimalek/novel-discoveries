import SlimG449Data

namespace G449OrbitArithmetic

set_option maxRecDepth 32768
set_option maxHeartbeats 120000000

theorem all_steps_arithmetic :
    (List.range 49).all (orbitStepBool dirs parent roots) = true := by decide +kernel

theorem checkedPowersArithmetic : testPowers powers = true := by decide +kernel

#print axioms all_steps_arithmetic
#print axioms checkedPowersArithmetic

end G449OrbitArithmetic
