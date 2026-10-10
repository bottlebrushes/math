import OAI.Probability.MatroidProphet.Residual.MaskUnion
import OAI.Probability.MatroidProphet.Pivots.Entropy
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

namespace MatroidProphet
open Finset Pivots
variable {α : Type*} [DecidableEq α]

lemma log_three_le : Real.log 3 ≤ 65 / 41 * Real.log 2 := by
  have h : Real.log ((3 : ℝ) ^ 41) ≤ Real.log ((2 : ℝ) ^ 65) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- The residual exponent at `κ = ruleKappa` is charged `10 log 2` by the threshold
`residualDelta` at every analyzed group size. -/
lemma residual_tail_coefficient (N : ℝ) (hN : densityThreshold ≤ N) :
    (residualExponent ruleKappa - residualDelta * Real.log 2) * N ≤ -(10 * Real.log 2) := by
  rw [residualExponent_charge]
  have hlog := Real.log_two_gt_d9
  have h3 := log_three_le
  have hcoef : (5 + 5 * Real.log 3 + 49 * Real.log 2) / 1536 - residualDelta * Real.log 2 ≤
      (5 - 1602 / 41 * Real.log 2) / 1536 := by
    unfold residualDelta; linarith
  have hneg : (5 - 1602 / 41 * Real.log 2) / 1536 ≤ 0 := by nlinarith
  have hN' : (1536 : ℝ) ≤ N := by simpa [densityThreshold, ruleKappa] using hN
  have hm := mul_le_mul_of_nonpos_left hN' hneg
  have hN0 : 0 ≤ N := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef hN0]

/-- Union-bound tail for the sharp parameters. -/
theorem bitsExpectation_residualBad_tail (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp (residualExponent ruleKappa * V.card))
    (hn : densityThreshold ≤ (V.card : ℝ)) :
    bitsExpectation q V (residualBadIndicator F (residualDelta * V.card)) ≤ residualTail := by
  have htail := bitsExpectation_residualBad_le q hq0 hqhalf V F hF (residualDelta * V.card)
  have hmul := mul_le_mul_of_nonneg_right hcard
    (Real.exp_nonneg (-(residualDelta * V.card) * Real.log 2))
  apply htail.trans (hmul.trans ?_)
  rw [← Real.exp_add]
  have hexp := residual_tail_coefficient _ hn
  calc
    Real.exp (residualExponent ruleKappa * V.card + -(residualDelta * V.card) * Real.log 2)
        ≤ Real.exp (-(10 * Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
    _ = residualTail := by
        rw [Real.exp_neg, show (10 : ℝ) * Real.log 2 = ((10 : ℕ) : ℝ) * Real.log 2 by norm_num,
          Real.exp_nat_mul, Real.exp_log (by norm_num)]
        norm_num [residualTail]

end MatroidProphet

end OAI
