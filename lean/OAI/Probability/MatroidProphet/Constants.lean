import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace OAI

namespace MatroidProphet

noncomputable section

/-- Geometric level ratio `B`. -/
def weightBase : ℝ := 2 ^ 6
/-- Density rank charge `κ`; the rule uses the natural number `2^12`. -/
def densityThreshold : ℝ := 2 ^ 12
/-- Guard and test mask rate `t`. -/
def thinningRate : ℝ := ((2 : ℝ) ^ 19)⁻¹
/-- Candidate-filter mask rate `p_H`. -/
def filterRate : ℝ := 13 / 16
/-- Density mask rate `p_D`. -/
def densityRate : ℝ := 15 / 32
/-- Probability of the maximum branch. -/
def branchRate : ℝ := ((2 : ℝ) ^ 14)⁻¹
/-- Low-hazard threshold of the paper's exit lemma (Lemma 4.2). -/
def exitThreshold : ℝ := ((2 : ℝ) ^ 12)⁻¹
/-- Squared exit mass per nonloop label. -/
def exitMass : ℝ := 6 / 25
/-- Sample-to-rank coefficient `g = p_D · s / 2`. -/
def retainedFraction : ℝ := 9 / 160
/-- Bound on the probability of the bad residual event. -/
def residualTail : ℝ := ((2 : ℝ) ^ 10)⁻¹
/-- Coefficient of the group size in the transfer lemma. -/
def transferError : ℝ := 213 / 10000
/-- Coefficient of the candidate mass in the weighted payoff. -/
def payoffError : ℝ := 367 / 10000
/-- Small-maximum threshold factor `ε`; the threshold is `ε (1 - p_H) / κ`. -/
def smallFraction : ℝ := ((2 : ℝ) ^ 8)⁻¹

/-- Success probability of the maximum rule, whose mask is the filter mask: the top label is
unmasked and the second one masked. -/
def maximumFactor : ℝ := filterRate * (1 - filterRate)

/-- Small-maximum threshold `θ`. -/
def smallThreshold : ℝ := smallFraction * (1 - filterRate) / densityThreshold

/-- The main-branch fraction of the rounded optimum. -/
def mainFraction : ℝ :=
  (1 - 1 / weightBase) * (thinningRate / densityThreshold) * (1 - filterRate) *
    (retainedFraction * (1 - smallFraction * (weightBase / (weightBase - 1))) -
      payoffError / filterRate)

theorem constants_positive : 0 < weightBase ∧ 0 < densityThreshold ∧
    0 < thinningRate ∧ 0 < exitThreshold ∧ 0 < retainedFraction := by
  norm_num [weightBase, densityThreshold, thinningRate, exitThreshold, retainedFraction]

lemma rates_mem : 0 < filterRate ∧ filterRate < 1 ∧ 0 < densityRate ∧ densityRate < 1 ∧
    0 < branchRate ∧ branchRate < 1 ∧ thinningRate ≤ 1 := by
  norm_num [filterRate, densityRate, branchRate, thinningRate]

lemma retainedFraction_eq : retainedFraction = densityRate * exitMass / 2 := by
  norm_num [retainedFraction, densityRate, exitMass]

lemma payoffError_ge :
    transferError + thinningRate * densityThreshold +
      (thinningRate * densityThreshold + densityRate) / (weightBase - 1) ≤ payoffError := by
  norm_num [transferError, thinningRate, densityThreshold, densityRate, weightBase, payoffError]

lemma maskUnion_le_half : densityRate + (1 - densityRate) * thinningRate ≤ 1 / 2 := by
  norm_num [densityRate, thinningRate]

lemma mainFraction_nonneg : 0 ≤ mainFraction := by
  norm_num [mainFraction, weightBase, thinningRate, densityThreshold, filterRate,
    retainedFraction, smallFraction, payoffError]

lemma smallThreshold_nonneg : 0 ≤ smallThreshold := by
  norm_num [smallThreshold, smallFraction, filterRate, densityThreshold]

/-- Final constant, main case: the main branch carries `2^-46` after rounding. -/
theorem hidden_fraction_main :
    ((2 : ℝ) ^ 46)⁻¹ * weightBase ≤ (1 - branchRate) * mainFraction := by
  norm_num [mainFraction, weightBase, thinningRate, densityThreshold, filterRate,
    retainedFraction, smallFraction, payoffError, branchRate]

/-- Final constant, maximum case. -/
theorem hidden_fraction_maximum :
    ((2 : ℝ) ^ 46)⁻¹ * weightBase ≤ branchRate * (maximumFactor * smallThreshold) := by
  norm_num [smallThreshold, smallFraction, filterRate, densityThreshold, branchRate, weightBase,
    maximumFactor]

theorem public_fraction_slack : ((2 : ℝ) ^ 310)⁻¹ ≤ ((2 : ℝ) ^ 46)⁻¹ := by
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- Mixing the two branches with the biased branch coin. -/
theorem branch_mixture_lower (W maximumWeight mainPayoff maximumPayoff : ℝ)
    (hW : 0 ≤ W) (hmw : 0 ≤ maximumWeight) (hmain : 0 ≤ mainPayoff)
    (hmax : maximumFactor * maximumWeight ≤ maximumPayoff)
    (hsmall : maximumWeight ≤ smallThreshold * W → mainFraction * W ≤ mainPayoff) :
    ((2 : ℝ) ^ 46)⁻¹ * weightBase * W ≤
      (1 - branchRate) * mainPayoff + branchRate * maximumPayoff := by
  have hr := rates_mem
  have hf : 0 ≤ maximumFactor := by norm_num [maximumFactor, filterRate]
  have hmaxp : 0 ≤ maximumPayoff := le_trans (mul_nonneg hf hmw) hmax
  by_cases hm : maximumWeight ≤ smallThreshold * W
  · have hs := hsmall hm
    have h1 := mul_le_mul_of_nonneg_right hidden_fraction_main hW
    have h2 : (1 - branchRate) * (mainFraction * W) ≤ (1 - branchRate) * mainPayoff :=
      mul_le_mul_of_nonneg_left hs (by linarith)
    nlinarith [mul_nonneg hr.2.2.2.2.1.le hmaxp]
  · have hm' : smallThreshold * W < maximumWeight := lt_of_not_ge hm
    have h1 := mul_le_mul_of_nonneg_right hidden_fraction_maximum hW
    have h3 : maximumFactor * (smallThreshold * W) ≤ maximumFactor * maximumWeight :=
      mul_le_mul_of_nonneg_left hm'.le hf
    have h2 : branchRate * (maximumFactor * (smallThreshold * W)) ≤ branchRate * maximumPayoff :=
      mul_le_mul_of_nonneg_left (h3.trans hmax) hr.2.2.2.2.1.le
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - branchRate) hmain]

end

end MatroidProphet

end OAI
