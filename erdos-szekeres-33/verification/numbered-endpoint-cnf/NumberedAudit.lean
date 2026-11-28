import NumberedCNF

namespace ES33.Numbering

private def auditSign : EndpointVar 3 := .sign 0 1 2
private def auditPair : EndpointVar 3 := .capPair 3 0 2

/-- A cap projection with the 3-cap state aliased to a negative sign,
plus units enforcing that negative sign and denying its pair state. -/
def auditFormula : CNF (EndpointVar 3) :=
  [[⟨auditSign,true⟩,⟨auditPair,true⟩],
   [⟨auditSign,false⟩], [⟨auditPair,false⟩]]

private def auditKeys : List (EndpointVar 3) := variableTable auditFormula

private theorem auditCover : Supports auditKeys auditFormula :=
  variableTable_supports auditFormula

theorem audit_exact_rows :
    (emit auditKeys auditFormula auditCover).parse = some [[1,2],[-1],[-2]] := by
  decide

theorem audit_exact_header_and_terminators :
    (emit auditKeys auditFormula auditCover).numVars = 2 ∧
    (emit auditKeys auditFormula auditCover).numClauses = 3 ∧
    (emit auditKeys auditFormula auditCover).rows = [[1,2,0],[-1,0],[-2,0]] := by
  decide

private theorem audit_numbered_unsat :
    ¬ ∃ a, NumberedSatisfies a [[1,2],[-1],[-2]] := by
  rintro ⟨a,h⟩
  have h₁ := h [-1] (by decide)
  have h₂ := h [-2] (by decide)
  have h₃ := h [1,2] (by decide)
  simp [numberedHolds] at h₁ h₂ h₃
  cases h₃ <;> simp_all

theorem audit_typed_unsat :
    ¬ ∃ a, Satisfies a auditFormula :=
  of_checked_numbered_unsat auditKeys auditFormula auditCover _
    audit_exact_rows audit_numbered_unsat

#print axioms audit_exact_rows
#print axioms audit_exact_header_and_terminators
#print axioms audit_typed_unsat

end ES33.Numbering
