import C14GlobalDriverDraft
import C14GlobalChunkData0024_0048

namespace Euler.C14.Production
open Euler.C14.IndexedDraft
set_option maxHeartbeats 2400000
set_option maxRecDepth 18000

global_rup first 8825 rows0_24
global_rup second 8849 rows24_48

theorem first48 (base : Sat.Fmla) : Slice base rowAt 8825 8873 :=
  compose (first base) (second base)

#print axioms first
#print axioms second
#print axioms first48
end Euler.C14.Production
