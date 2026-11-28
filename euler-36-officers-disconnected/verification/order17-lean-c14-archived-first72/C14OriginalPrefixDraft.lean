import C14OriginalSpans00Draft
import C14OriginalSpans01Draft
import C14OriginalSpans02Draft
import C14OriginalSpans03Draft
import C14OriginalSpans04Draft
import C14OriginalSpans05Draft
import C14OriginalSpans06Draft
import C14OriginalSpans07Draft
import C14OriginalSpans08Draft
import C14GlobalFirstTwoDraft
namespace Euler.C14.Production
open Euler.C14.IndexedDraft
set_option maxRecDepth 18000
theorem exactSortedArchiveInitial : GoodBelow archivedGlobalCore rowAt 8825 :=
  prefixOfZeroSpan (spanJoin (spanJoin (spanJoin (spanJoin (spanJoin (spanJoin originalSpan0 originalSpan1) (spanJoin originalSpan2 originalSpan3)) (spanJoin (spanJoin originalSpan4 originalSpan5) (spanJoin originalSpan6 originalSpan7))) (spanJoin (spanJoin (spanJoin originalSpan8 originalSpan9) (spanJoin originalSpan10 originalSpan11)) (spanJoin (spanJoin originalSpan12 originalSpan13) (spanJoin originalSpan14 (spanJoin originalSpan15 originalSpan16))))) (spanJoin (spanJoin (spanJoin (spanJoin originalSpan17 originalSpan18) (spanJoin originalSpan19 originalSpan20)) (spanJoin (spanJoin originalSpan21 originalSpan22) (spanJoin originalSpan23 originalSpan24))) (spanJoin (spanJoin (spanJoin originalSpan25 originalSpan26) (spanJoin originalSpan27 originalSpan28)) (spanJoin (spanJoin originalSpan29 originalSpan30) (spanJoin originalSpan31 (spanJoin originalSpan32 originalSpan33)))))) (spanJoin (spanJoin (spanJoin (spanJoin (spanJoin originalSpan34 originalSpan35) (spanJoin originalSpan36 originalSpan37)) (spanJoin (spanJoin originalSpan38 originalSpan39) (spanJoin originalSpan40 originalSpan41))) (spanJoin (spanJoin (spanJoin originalSpan42 originalSpan43) (spanJoin originalSpan44 originalSpan45)) (spanJoin (spanJoin originalSpan46 originalSpan47) (spanJoin originalSpan48 (spanJoin originalSpan49 originalSpan50))))) (spanJoin (spanJoin (spanJoin (spanJoin originalSpan51 originalSpan52) (spanJoin originalSpan53 originalSpan54)) (spanJoin (spanJoin originalSpan55 originalSpan56) (spanJoin originalSpan57 (spanJoin originalSpan58 originalSpan59)))) (spanJoin (spanJoin (spanJoin originalSpan60 originalSpan61) (spanJoin originalSpan62 originalSpan63)) (spanJoin (spanJoin originalSpan64 originalSpan65) (spanJoin originalSpan66 (spanJoin originalSpan67 originalSpan68)))))))
theorem first48_fromExactGlobalArchive : GoodBelow archivedGlobalCore rowAt 8873 :=
  first48 archivedGlobalCore exactSortedArchiveInitial
#print axioms exactSortedArchiveInitial
#print axioms first48_fromExactGlobalArchive
end Euler.C14.Production
