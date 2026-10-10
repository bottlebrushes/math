import OAI.Probability.MatroidProphet.Residual.MaskUnion
import OAI.Probability.MatroidProphet.Pivots.Entropy
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

namespace MatroidProphet
open Finset Pivots
variable {α : Type*} [DecidableEq α]

/-- Union-bound tail for the sharp parameters. -/
theorem bitsExpectation_residualBad_tail (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp (residualExponent (2 ^ 12) * V.card))
    (hn : (2 : ℝ) ^ 12 ≤ (V.card : ℝ)) :
    bitsExpectation q V (residualBadIndicator F (residualDelta * V.card)) ≤ residualTail := by
  have htail := bitsExpectation_residualBad_le q hq0 hqhalf V F hF (residualDelta * V.card)
  have hmul := mul_le_mul_of_nonneg_right hcard
    (Real.exp_nonneg (-(residualDelta * V.card) * Real.log 2))
  apply htail.trans (hmul.trans ?_)
  rw [← Real.exp_add, residualExponent_charge]
  have hlog := Real.log_two_gt_d9
  have hcoef : (5 + 64 * Real.log 2) / 4096 - residualDelta * Real.log 2 ≤ 0 := by
    unfold residualDelta; nlinarith
  have hexp : (5 + 64 * Real.log 2) / 4096 * V.card + -(residualDelta * V.card) * Real.log 2 ≤
      -(10 * Real.log 2) := by
    have hm := mul_le_mul_of_nonpos_left hn hcoef
    have : (5 + 64 * Real.log 2) / 4096 * 2 ^ 12 - residualDelta * Real.log 2 * 2 ^ 12 ≤
        -(10 * Real.log 2) := by unfold residualDelta; norm_num; nlinarith
    nlinarith
  calc
    Real.exp ((5 + 64 * Real.log 2) / 4096 * V.card + -(residualDelta * V.card) * Real.log 2)
        ≤ Real.exp (-(10 * Real.log 2)) := Real.exp_le_exp.mpr hexp
    _ = residualTail := by
        rw [Real.exp_neg, show (10 : ℝ) * Real.log 2 = ((10 : ℕ) : ℝ) * Real.log 2 by norm_num,
          Real.exp_nat_mul, Real.exp_log (by norm_num)]
        norm_num [residualTail]

end MatroidProphet

end OAI
