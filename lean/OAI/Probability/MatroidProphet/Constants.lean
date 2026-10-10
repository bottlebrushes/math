import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace OAI

namespace MatroidProphet

noncomputable section

/-- Geometric level ratio `B`. -/
def weightBase : ℝ := 2 ^ 8
def ruleKappa : ℕ := 1536
/-- Density rank charge `κ`; the rule uses `ruleKappa`. -/
def densityThreshold : ℝ := (ruleKappa : ℝ)
/-- Guard and test mask rate `t`. -/
def thinningRate : ℝ := ((2 : ℝ) ^ 16)⁻¹
/-- Candidate-filter mask rate `p_H`. -/
def filterRate : ℝ := 3 / 4
/-- Density mask rate `p_D`. -/
def densityRate : ℝ := 7 / 16
/-- Probability of the maximum branch. -/
def branchRate : ℝ := ((2 : ℝ) ^ 9)⁻¹
/-- Low-hazard threshold of the paper's exit lemma (Lemma 4.2). -/
def exitThreshold : ℝ := ((2 : ℝ) ^ 12)⁻¹
/-- Squared exit mass per nonloop label. -/
def exitMass : ℝ := 67 / 250
/-- Sample-to-rank coefficient `g = p_D · s / 2`. -/
def retainedFraction : ℝ := 469 / 8000
/-- Bound on the probability of the bad residual event. -/
def residualTail : ℝ := ((2 : ℝ) ^ 10)⁻¹
/-- Expected captured residual per label: `Λ/log(1/p_O) + 1/((1-p_O)κ)` plus the cap tail. -/
def residualError : ℝ := 2005 / 100000
/-- Coefficient of the group size in the transfer lemma. -/
def transferError : ℝ := 101 / 5000
/-- Cap on the density-generator budget: `⌊|U|/2⌋ / κ`. -/
def capBudget (n : ℕ) : ℕ := n / 2 / ruleKappa
/-- Coefficient of the candidate mass in the weighted payoff. -/
def payoffError : ℝ := 3373 / 100000
/-- Small-maximum threshold factor `ε`; the threshold is `ε (1 - p_H) / κ`. -/
def smallFraction : ℝ := ((2 : ℝ) ^ 10)⁻¹

lemma ruleKappa_pos : 0 < ruleKappa := by
  norm_num [ruleKappa]

lemma two_le_ruleKappa : 2 ≤ ruleKappa := by
  norm_num [ruleKappa]

lemma ruleKappa_cast : ((ruleKappa : ℕ) : ℝ) = densityThreshold := by
  rfl

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
  norm_num [weightBase, densityThreshold, ruleKappa, thinningRate, exitThreshold,
    retainedFraction]

lemma rates_mem : 0 < filterRate ∧ filterRate < 1 ∧ 0 < densityRate ∧ densityRate < 1 ∧
    0 < branchRate ∧ branchRate < 1 ∧ thinningRate ≤ 1 := by
  norm_num [filterRate, densityRate, branchRate, thinningRate]

lemma retainedFraction_eq : retainedFraction = densityRate * exitMass / 2 := by
  norm_num [retainedFraction, densityRate, exitMass]

lemma payoffError_ge :
    transferError + thinningRate * densityThreshold / 2 +
      (thinningRate * densityThreshold + densityRate) / (weightBase - 1) ≤ payoffError := by
  norm_num [transferError, thinningRate, densityThreshold, ruleKappa, densityRate,
    weightBase, payoffError]

/-- Rate of the observed mask `D ∪ C` inside a group. -/
def maskUnionRate : ℝ := densityRate + (1 - densityRate) * thinningRate

lemma maskUnion_le_half : densityRate + (1 - densityRate) * thinningRate ≤ 1 / 2 := by
  norm_num [densityRate, thinningRate]

lemma maskUnionRate_pos : 0 < maskUnionRate := by
  norm_num [maskUnionRate, densityRate, thinningRate]

lemma mainFraction_nonneg : 0 ≤ mainFraction := by
  norm_num [mainFraction, weightBase, thinningRate, densityThreshold, ruleKappa, filterRate,
    retainedFraction, smallFraction, payoffError]

lemma smallThreshold_nonneg : 0 ≤ smallThreshold := by
  norm_num [smallThreshold, smallFraction, filterRate, densityThreshold, ruleKappa]

/-- Fraction of the rounded optimum guaranteed by the mixed rule; after the random rounding
offset it becomes `2^-38` of the true optimum. -/
def roundedFraction : ℝ := ((2 : ℝ) ^ 38)⁻¹ * (8 * weightBase / (weightBase - 1))

lemma roundedFraction_nonneg : 0 ≤ roundedFraction := by
  norm_num [roundedFraction, weightBase]

/-- Final constant, main case. -/
theorem hidden_fraction_main :
    roundedFraction ≤ (1 - branchRate) * mainFraction := by
  norm_num [roundedFraction, mainFraction, weightBase, thinningRate, densityThreshold,
    ruleKappa, filterRate, retainedFraction, smallFraction, payoffError, branchRate]

/-- Final constant, maximum case. -/
theorem hidden_fraction_maximum :
    roundedFraction ≤ branchRate * (maximumFactor * smallThreshold) := by
  norm_num [roundedFraction, smallThreshold, smallFraction, filterRate, densityThreshold,
    ruleKappa, branchRate, weightBase, maximumFactor]

/-- Without the offset, the rule keeps `2^-46` of the true optimum. -/
theorem plain_fraction : ((2 : ℝ) ^ 46)⁻¹ * weightBase ≤ roundedFraction := by
  norm_num [roundedFraction, weightBase]

/-- With the offset: `roundedFraction · (1 - 2^-8)/8 = 2^-38`. -/
theorem offset_fraction : roundedFraction * ((1 - 1 / 2 ^ 8) / 8) = ((2 : ℝ) ^ 38)⁻¹ := by
  norm_num [roundedFraction, weightBase]

theorem public_fraction_slack : ((2 : ℝ) ^ 310)⁻¹ ≤ ((2 : ℝ) ^ 38)⁻¹ := by
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- Mixing the two branches with the biased branch coin. -/
theorem branch_mixture_lower (W maximumWeight mainPayoff maximumPayoff : ℝ)
    (hW : 0 ≤ W) (hmw : 0 ≤ maximumWeight) (hmain : 0 ≤ mainPayoff)
    (hmax : maximumFactor * maximumWeight ≤ maximumPayoff)
    (hsmall : maximumWeight ≤ smallThreshold * W → mainFraction * W ≤ mainPayoff) :
    roundedFraction * W ≤
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
