/-- A rise of the actual output across a tied positive/negative input pair
forces a rise through the positive port even with the negative port held
fixed arbitrarily. No restriction is put on the other input coordinates. -/
theorem fixed_negative_port_pivot
    {Y : Type} (context : Y → Bool → Bool → Bool)
    (monoNeg : ∀ y x, context y x false = true → context y x true = true)
    (y : Y) (lo : context y false true = false)
    (hi : context y true false = true) (neg : Bool) :
    context y false neg = false ∧ context y true neg = true := by
  cases neg
  · refine ⟨?_, hi⟩
    cases hc : context y false false with
    | false => rfl
    | true =>
      have impossible : false = true := lo.symm.trans (monoNeg y false hc)
      cases impossible
  · exact ⟨lo, monoNeg y true hi⟩

/-- Eliminating a positively essential input from every positive port is
impossible, even if the negative port still occurs in the circuit. -/
theorem positively_essential_implies_positive_port
    {Y : Type} (context : Y → Bool → Bool → Bool)
    (monoNeg : ∀ y x, context y x false = true → context y x true = true)
    (y : Y) (lo : context y false true = false)
    (hi : context y true false = true) :
    ¬ (∀ y n, context y false n = context y true n) := by
  intro h
  obtain ⟨a, b⟩ := fixed_negative_port_pivot context monoNeg y lo hi false
  have impossible : false = true := a.symm.trans ((h y false).trans b)
  cases impossible

#print axioms fixed_negative_port_pivot
#print axioms positively_essential_implies_positive_port
