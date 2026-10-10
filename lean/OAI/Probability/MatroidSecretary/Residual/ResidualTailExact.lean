import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! The effective numerical tail of the sharpened `eq:residual-tail`, valid already at the
threshold group size `κ = ruleKappa`. -/

namespace MatroidProphet.SourceProof

/-- Exact effective exponential bound at every analyzed group size. -/
theorem residual_tail_exact (N : ℝ) (hN : densityThreshold ≤ N) :
    Real.exp ((Pivots.residualExponent ruleKappa - residualDelta * Real.log 2) * N) ≤
      residualTail := by
  have hexp := residual_tail_coefficient N hN
  calc
    _ ≤ Real.exp (-(10 * Real.log 2)) := Real.exp_le_exp.mpr hexp
    _ = residualTail := by
        rw [Real.exp_neg, show (10 : ℝ) * Real.log 2 = ((10 : ℕ) : ℝ) * Real.log 2 by norm_num,
          Real.exp_nat_mul, Real.exp_log (by norm_num)]
        norm_num [residualTail]

end MatroidProphet.SourceProof

end OAI
