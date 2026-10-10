import OAI.Probability.MatroidProphet.Algorithm.WeightedPayoff
import OAI.Probability.MatroidProphet.CompletePayoff
import OAI.Probability.MatroidProphet.Reduction
import OAI.Probability.MatroidProphet.Offset

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset MainAlgorithm

lemma main_branch_guarantee_small {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n)
    (hm : maximumRounded M w ≤
      smallThreshold * optimum M (fun e => roundedWeight weightBase (w e))) :
    mainFraction * optimum M (fun e => roundedWeight weightBase (w e)) ≤ mainPayoff M hE w := by
  apply main_branch_from_filter Finset.univ
    (analyzedComparisonMass M (fun e => roundedLevel weightBase (w e)))
    (comparisonMass M (fun e => roundedLevel weightBase (w e)))
    (fun H => ∑ e ∈ candidateLabels M (fun e => roundedLevel weightBase (w e)) H,
      roundedWeight weightBase (w e))
    (fun H => mainMean ⟨H, ∅, ∅, ∅, false⟩
      (fun d => mainWorstRounded M hE d (fun e => roundedLevel weightBase (w e))))
    (optimum M (fun e => roundedWeight weightBase (w e))) (maximumRounded M w)
    (optimum_nonneg M _) hm
  · exact expectation_positiveGreedy_survivors M hE w (by norm_num [weightBase])
  · exact expectation_candidateLabels_le_optimum M hE w weightBase
  · intro H _
    exact small_comparison_mass M hE w H
  · intro H _
    exact conditional_main_payoff M hE ⟨H, ∅, ∅, ∅, false⟩ _

/-- The mixed rule keeps `roundedFraction` of the optimum of the rounded weights. -/
theorem rounded_hidden_guarantee {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    roundedFraction * optimum M (fun e => roundedWeight weightBase (w e)) ≤
      ∫ r, hiddenWorstReward (completeHiddenRule M hE) w r ∂sourceSeedLaw n := by
  have hb := branch_mixture_lower _ (maximumRounded M w) (mainPayoff M hE w) (maximumPayoff M w)
    (optimum_nonneg M _) (maximumRounded_nonneg M w) (mainPayoff_nonneg M hE w)
    (maximum_branch_guarantee M w hw) (main_branch_guarantee_small M hE w)
  exact hb.trans (integrated_branch_lower M hE w hw)

/-- Without the random offset the rule keeps `2⁻⁴⁷` of the true optimum. -/
theorem complete_hidden_guarantee {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    ((2 : ℝ) ^ 47)⁻¹ * optimum M w ≤
      ∫ r, hiddenWorstReward (completeHiddenRule M hE) w r ∂sourceSeedLaw n := by
  let W := optimum M (fun e => roundedWeight weightBase (w e))
  have hr := optimum_rounding_bound M weightBase (by norm_num [weightBase]) w hw
  have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ 47)⁻¹)
  have hW : 0 ≤ W := optimum_nonneg M _
  have hplain := mul_le_mul_of_nonneg_right plain_fraction hW
  calc ((2 : ℝ) ^ 47)⁻¹ * optimum M w ≤ ((2 : ℝ) ^ 47)⁻¹ * (weightBase * W) := hscaled
    _ = ((2 : ℝ) ^ 47)⁻¹ * weightBase * W := by ring
    _ ≤ roundedFraction * W := hplain
    _ ≤ _ := rounded_hidden_guarantee M hE w hw

/-- The sharpened rule: the mixed rule run on weights scaled by a random power `2^{-m}`,
`m ∈ {0, …, 7}`. -/
noncomputable def sharpHiddenRule {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    HiddenRule n (mainSeedBits n + 3) :=
  offsetHiddenRule (completeHiddenRule M hE)

/-- The sharpened rule keeps `2⁻⁴²` of the optimum against the full-seed adversary. -/
theorem sharp_hidden_guarantee {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    ((2 : ℝ) ^ 42)⁻¹ * optimum M w ≤
      ∫ r, hiddenWorstReward (sharpHiddenRule M hE) w r ∂offsetSeedLaw (sourceSeedLaw n) := by
  have h := offset_guarantee M (completeHiddenRule M hE) (sourceSeedLaw n) roundedFraction
    roundedFraction_nonneg (fun v hv => by
      simpa only [weightBase] using rounded_hidden_guarantee M hE v hv) w hw
  rwa [offset_fraction] at h

theorem hidden_vector_sharp : HiddenVectorChallengeSharp := by
  intro n M hE
  refine ⟨mainSeedBits n + 3, offsetSeedLaw (sourceSeedLaw n), inferInstance,
    sharpHiddenRule M hE, ?_, ?_⟩
  · exact offsetHiddenRule_feasible M _ (completeHiddenRule_feasible M hE)
  · exact sharp_hidden_guarantee M hE

theorem hidden_vector : HiddenVectorChallenge :=
  hiddenVectorChallengeSharp_implies_hiddenVectorChallenge hidden_vector_sharp

/-- The one-sample matroid prophet inequality with the sharpened constant `2⁻⁴²`. -/
theorem one_sample_sharp.{u} : OneSampleChallengeSharp.{u} :=
  hiddenVectorChallengeSharp_implies_oneSampleChallengeSharp hidden_vector_sharp

theorem one_sample.{u} : OneSampleChallenge.{u} :=
  hiddenVectorChallenge_implies_oneSampleChallenge hidden_vector

end MatroidProphet

end OAI
