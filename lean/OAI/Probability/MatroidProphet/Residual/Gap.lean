import OAI.Probability.MatroidProphet.Residual.Deterministic

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α : Type*} [Fintype α] [LinearOrder α]

lemma safeLayerStatistic_le_ncard
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2) :
    safeLayerStatistic M hE κ D C T h U I ε ≤ U.ncard := by
  let L := safeLayerSet M hE κ D C T h U I ε
  have hd : Pairwise (fun b c => Disjoint (L b) (L c)) := by
    intro b c hbc
    exact (nominalLayerSet_disjoint M hE κ D C h U ε hbc).mono
      (fun _ he => he.1.2) (fun _ he => he.1.2)
  have heq : (⋃ b, L b).ncard = ∑ b, (L b).ncard := by
    simpa only [finsum_eq_sum_of_fintype] using
      Set.ncard_iUnion_of_finite (fun b => Set.toFinite (L b)) hd
  rw [show safeLayerStatistic M hE κ D C T h U I ε = ∑ b, (L b).ncard from rfl, ← heq]
  apply Set.ncard_le_ncard _ (Set.toFinite U)
  intro e he
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp he
  exact hb.1.2.1

noncomputable def nominalTransferGap (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O I : Set α) (ε : Fin 2) : ℝ :=
  max ((safeLayerStatistic M hE κ D C T h U I ε : ℝ) -
    (κ : ℝ) * nominalRankStatistic M hE κ D C T h U O ε) 0

lemma safe_le_rank_add_gap
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U O I : Set α) (ε : Fin 2) :
    (safeLayerStatistic M hE κ D C T h U I ε : ℝ) ≤
      (κ : ℝ) * nominalRankStatistic M hE κ D C T h U O ε +
        nominalTransferGap M hE κ D C T h U O I ε := by
  have hx := le_max_left ((safeLayerStatistic M hE κ D C T h U I ε : ℝ) -
    (κ : ℝ) * nominalRankStatistic M hE κ D C T h U O ε) 0
  unfold nominalTransferGap
  linarith

end MatroidProphet

end OAI
