import OAI.Probability.MatroidProphet.Residual.LabeledFamily
import OAI.Probability.MatroidProphet.PathRankCost

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

lemma safeLayer_le_witness_residual
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (hI : I ⊆ D h)
    (ε : Fin 2) (b : ParityWindow (activation h) ε) (W : Set α) :
    (safeLayerSet M hE κ D C T h U I ε b).ncard ≤ κ * W.ncard +
      (nominalLayerSet M hE κ D C h U ε b \
        M.closure (nominalPath M hE κ D C h (b.val.val - 2) ∪
          lowerCompetition M hE κ D C T b.val.val h ∪ W)).ncard := by
  by_cases hv : activation h + 2 ≤ b.val.val ∧ b.val.val ≤ 0
  · have hx : nominalPath M hE κ D C h (b.val.val - 2) =
        densityExpansion M hE κ (D h) (guardedPath M hE κ D C h (b.val.val - 2)) := by
      unfold nominalPath densityEnabled
      rw [ite_eq_left (by omega)]
    rw [hx]
    apply safe_layer_le_witness_residual M hE κ (D h)
      (guardedPath M hE κ D C h (b.val.val - 2)) (lowerCompetition M hE κ D C T b.val.val h)
      W (nominalLayerSet M hE κ D C h U ε b) (safeLayerSet M hE κ D C T h U I ε b)
    intro e he
    exact ⟨⟨hI he.1.1, he.1.2⟩, he.2⟩
  · have he : nominalLayerSet M hE κ D C h U ε b = ∅ := by
      ext e
      constructor
      · exact fun he => (hv ⟨he.2.1, he.2.2.1⟩).elim
      · simp
    simp [safeLayerSet, he]

lemma safeStatistic_le_witness_residual (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (hI : I ⊆ D h)
    (ε : Fin 2) (W : ParityWindow (activation h) ε → Set α) :
    safeLayerStatistic M hE κ D C T h U I ε ≤ κ * (∑ b, (W b).ncard) +
      (nominalResidualSet M hE κ D C T h U ε W).ncard := by
  unfold safeLayerStatistic
  calc
    _ ≤ ∑ b, (κ * (W b).ncard +
        (nominalLayerSet M hE κ D C h U ε b \
          M.closure ((nominalPath M hE κ D C h (b.val.val - 2) ∪
            lowerCompetition M hE κ D C T b.val.val h) ∪ W b)).ncard) :=
      sum_le_sum (fun b _ => safeLayer_le_witness_residual M hE κ D C T h U I hI ε b (W b))
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, ← residualUnion_ncard M _ _ W
        (nominalLayerSet_disjoint M hE κ D C h U ε)]
      rfl

end MatroidProphet

end OAI
