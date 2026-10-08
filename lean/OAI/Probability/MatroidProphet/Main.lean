import OAI.Probability.MatroidProphet.Algorithm.WeightedPayoff
import OAI.Probability.MatroidProphet.CompletePayoff
import OAI.Probability.MatroidProphet.Reduction

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

theorem complete_hidden_guarantee {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    ((2 : ℝ) ^ 46)⁻¹ * optimum M w ≤
      ∫ r, hiddenWorstReward (completeHiddenRule M hE) w r ∂sourceSeedLaw n := by
  let W := optimum M (fun e => roundedWeight weightBase (w e))
  have hb := branch_mixture_lower W (maximumRounded M w) (mainPayoff M hE w) (maximumPayoff M w)
    (optimum_nonneg M _) (maximumRounded_nonneg M w) (mainPayoff_nonneg M hE w)
    (maximum_branch_guarantee M w hw) (main_branch_guarantee_small M hE w)
  have hi := integrated_branch_lower M hE w hw
  have hr := optimum_rounding_bound M weightBase (by norm_num [weightBase]) w hw
  have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ 46)⁻¹)
  have hcancel : ((2 : ℝ) ^ 46)⁻¹ * (weightBase * W) = ((2 : ℝ) ^ 46)⁻¹ * weightBase * W := by ring
  rw [hcancel] at hscaled
  exact hscaled.trans (hb.trans hi)

theorem hidden_vector_sharp : HiddenVectorChallengeSharp := by
  intro n M hE
  refine ⟨mainSeedBits n, sourceSeedLaw n, inferInstance, completeHiddenRule M hE, ?_, ?_⟩
  · exact completeHiddenRule_feasible M hE
  · exact complete_hidden_guarantee M hE

theorem hidden_vector : HiddenVectorChallenge :=
  hiddenVectorChallengeSharp_implies_hiddenVectorChallenge hidden_vector_sharp

/-- The one-sample matroid prophet inequality with the sharpened constant `2⁻⁴⁶`. -/
theorem one_sample_sharp.{u} : OneSampleChallengeSharp.{u} :=
  hiddenVectorChallengeSharp_implies_oneSampleChallengeSharp hidden_vector_sharp

theorem one_sample.{u} : OneSampleChallenge.{u} :=
  hiddenVectorChallenge_implies_oneSampleChallenge hidden_vector

end MatroidProphet

end OAI
