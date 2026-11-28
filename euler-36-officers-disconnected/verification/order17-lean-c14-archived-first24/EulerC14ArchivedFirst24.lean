import EulerC14ArchivedDriver

namespace Euler.C14.IndexedDraft
set_option maxRecDepth 12000
set_option maxHeartbeats 2400000

archived_subsumes archivedSortedCore archive_subsumes_exact_local base
  (include_str "c14-sorted-core.cnf")
  #[1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,49,51,61,63,72,74,77,79,91,101,103,114,154,156,166,168,171,173,184,186,201,214,216,228,339,341,344,346,359,361,373,375,384,391,392,393,394,401,435,437,446,448,460,462,473,475,485,494,495,496,497,499,2095,3862,4503,6639,8027,8032,8038,8044,8049,8064,8065,8070,8074,8075,8145,8148,8152,8154,8158,8162,8166,8168,8174,8177,8181,8182,8184,8190,8193,8197,8198,8200,8201,8202,8203,8204,8205,8206,8207,8208,8209,8210,8211,8212,8213,8214,8215,8216,8217,8218,8219,8220,8233,8268,8294,8402]

theorem first24_fromExactArchivedCNF : GoodBelow archivedSortedCore rowAt 159 := by
  intro j hj v hv
  apply first24_fromExactLocalCNF j hj v
  exact ⟨fun c hc => hv.1 c (archive_subsumes_exact_local.1 c hc)⟩

#print axioms archive_subsumes_exact_local
#print axioms first24_fromExactArchivedCNF
end Euler.C14.IndexedDraft
