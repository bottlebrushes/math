import OAI.Probability.MatroidProphet.ModelSharp
import OAI.Probability.MatroidProphet.Statements
import OAI.Probability.MatroidProphet.Gluing
import Mathlib.Tactic.NormNum

namespace OAI

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

theorem hiddenVectorChallenge_implies_oneSampleChallenge.{u}
    (hh : HiddenVectorChallenge) : OneSampleChallenge.{u} := by
  intro n M hM
  obtain ⟨bits, ν, hν, A, hA, hbound⟩ := hh n M hM
  let := hν
  refine ⟨bits, ν, hν, sampleSimulation A, sampleSimulation_feasible M A hA, ?_⟩
  intro Ω mΩ μ hμ S V R hS hV hR hSN hVN hi hlaw hseed hRlaw hopt π hπ
  obtain ⟨hri, hpay⟩ := oneSample_of_hidden M A ν (((2 : ℝ) ^ 293)⁻¹) hA hbound
    μ S V R hS hV hR hSN hVN hi hlaw hseed hRlaw hopt π hπ
  refine ⟨hri, le_trans ?_ hpay⟩
  apply mul_le_mul_of_nonneg_right
  · exact inv_anti₀ (pow_pos (by norm_num : (0 : ℝ) < 2) 293)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 293 ≤ 310))
  · exact integral_nonneg fun ω => optimum_nonneg M (V ω)

theorem hiddenVectorChallengeSharp_implies_oneSampleChallengeSharp.{u}
    (hh : HiddenVectorChallengeSharp) : OneSampleChallengeSharp.{u} := by
  intro n M hM
  obtain ⟨bits, ν, hν, A, hA, hbound⟩ := hh n M hM
  let := hν
  refine ⟨bits, ν, hν, sampleSimulation A, sampleSimulation_feasible M A hA, ?_⟩
  intro Ω mΩ μ hμ S V R hS hV hR hSN hVN hi hlaw hseed hRlaw hopt π hπ
  exact oneSample_of_hidden M A ν (((2 : ℝ) ^ 41)⁻¹) hA hbound
    μ S V R hS hV hR hSN hVN hi hlaw hseed hRlaw hopt π hπ

theorem hiddenVectorChallengeSharp_implies_hiddenVectorChallenge
    (hh : HiddenVectorChallengeSharp) : HiddenVectorChallenge := by
  intro n M hM
  obtain ⟨bits, ν, hν, A, hA, hbound⟩ := hh n M hM
  refine ⟨bits, ν, hν, A, hA, fun w hw => le_trans ?_ (hbound w hw)⟩
  apply mul_le_mul_of_nonneg_right
  · exact inv_anti₀ (pow_pos (by norm_num : (0 : ℝ) < 2) 41)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 41 ≤ 293))
  · exact optimum_nonneg M w

end MatroidProphet

end OAI
