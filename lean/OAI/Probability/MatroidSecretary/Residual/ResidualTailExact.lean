import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! The effective numerical tail of the sharpened `eq:residual-tail`, valid already at the
threshold group size `κ = 2^12`. -/

namespace MatroidProphet.SourceProof

/-- Exact effective exponential bound at every analyzed group size. -/
theorem residual_tail_exact (N : ℝ) (hN : densityThreshold ≤ N) :
    Real.exp ((Pivots.residualExponent (2 ^ 12) - residualDelta * Real.log 2) * N) ≤
      residualTail := by
  have h := bitsExpectation_residualBad_tail (α := Fin 0) (fun _ => 0) (fun _ => le_rfl)
    (fun _ => by norm_num) ∅ ∅ (fun _ h => absurd h (Finset.notMem_empty _))
  rw [Pivots.residualExponent_charge]
  have hlog := Real.log_two_gt_d9
  have hN0 : 0 ≤ N := le_trans (by norm_num [densityThreshold]) hN
  have hcoef : (5 + 64 * Real.log 2) / 4096 - residualDelta * Real.log 2 ≤ 0 := by
    unfold residualDelta; nlinarith
  have hexp : ((5 + 64 * Real.log 2) / 4096 - residualDelta * Real.log 2) * N ≤
      -(10 * Real.log 2) := by
    have hm := mul_le_mul_of_nonpos_left hN hcoef
    unfold densityThreshold at hm
    have : ((5 + 64 * Real.log 2) / 4096 - residualDelta * Real.log 2) * 2 ^ 12 ≤
        -(10 * Real.log 2) := by unfold residualDelta; norm_num; nlinarith
    nlinarith
  calc
    _ ≤ Real.exp (-(10 * Real.log 2)) := Real.exp_le_exp.mpr hexp
    _ = residualTail := by
        rw [Real.exp_neg, show (10 : ℝ) * Real.log 2 = ((10 : ℕ) : ℝ) * Real.log 2 by norm_num,
          Real.exp_nat_mul, Real.exp_log (by norm_num)]
        norm_num [residualTail]

end MatroidProphet.SourceProof

end OAI
