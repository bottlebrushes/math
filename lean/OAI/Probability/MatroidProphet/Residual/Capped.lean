import OAI.Probability.MatroidProphet.Residual.Gap

/-!
# Residual families with a capped generator budget

The residual family of Lemma 5.3 is built for a budget `q` of density generators and rank
witnesses.  The manuscript uses `q = |U|/κ`; whenever the group's density sample has at most
`β|U|` labels, the smaller budget `q = ⌊β|U|⌋/κ` already captures every residual, and the
remaining event has exponentially small probability.  The transfer gap is bounded by the
largest captured residual, which is integrated by a layer-cake sum.
-/

namespace OAI

namespace MatroidProphet

open Set Finset Pivots

variable {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}

noncomputable def labeledResidualFamilyQ (M : Matroid α) (U : Finset α) (q : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) : Finset (Finset α) :=
  (integerResidualFamily M U q F a ε K (groupLabel U)).image (fun R => R.image (groupLabel U))

lemma labeledResidualFamilyQ_subsets (M : Matroid α) (U : Finset α) (q : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) :
    ∀ R ∈ labeledResidualFamilyQ M U q F a ε K, R ⊆ U := by
  rintro R hR e he
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
  exact groupLabel_mem U i

lemma labeledResidualFamilyQ_card (M : Matroid α) (hE : M.E = Set.univ)
    (U : Finset α) (hU : U.Nonempty) (q : ℕ) (κ : ℝ) (hκ : 2 ≤ κ)
    (hq : (q : ℝ) ≤ (U.card : ℝ) / κ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α) :
    ((labeledResidualFamilyQ M U q F a ε K).card : ℝ) ≤
      Real.exp (Pivots.residualExponent κ * U.card) := by
  obtain ⟨d, hd⟩ := hU
  have hc : (labeledResidualFamilyQ M U q F a ε K).card ≤
      (integerResidualFamily M U q F a ε K (groupLabel U)).card := Finset.card_image_le
  exact (show ((labeledResidualFamilyQ M U q F a ε K).card : ℝ) ≤
    (integerResidualFamily M U q F a ε K (groupLabel U)).card by exact_mod_cast hc).trans
      (card_residualFamily_le_exp M d U q _ _ _ _ (groupLabel U)
        (by simp [hE]) (by simp [hE]) (by simp [hE]) rfl κ hκ hq)

lemma nominal_residual_mem_familyQ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ)
    (U Z : Finset α) (hDU : D h ⊆ (U : Set α)) (hZU : Z ⊆ U) (q : ℕ)
    (hDq : (D h).ncard / κ ≤ q) (hZcard : Z.card ≤ q) (ε : Fin 2)
    (K : ParityWindow (activation h) ε → Set α)
    (hK : ∀ b, K b ⊆ guardedPath M hE κ D C h b.val.val)
    (β : Z → ParityWindow (activation h) ε)
    (hz : ∀ w, w.val ∈ nominalPath M hE κ D C h (β w).val.val)
    (test : Fin n → α) (hnonloop : ∀ f, test f ∉ M.closure ∅) :
    integerResidual M (nominalPath M hE κ D C h) test (activation h) ε K
        (fun w : Z => w.val) β ∈
      integerResidualFamily M U q (guardedPath M hE κ D C h)
        (activation h) ε K test := by
  classical
  obtain ⟨G, hGD, hGcard, τ, hτ, hgen⟩ := nominalPath_all_time_generators M hE κ hκ D C h
  let J : Finset α := G.toFinset
  let ν : J → ℤ := fun i => activation h + (τ i.val : ℤ)
  have hJ : J ⊆ U := by
    intro e he
    exact hDU (hGD (Set.mem_toFinset.mp he))
  have hJcard : J.card ≤ q := by
    refine le_trans ?_ hDq
    apply (Nat.le_div_iff_mul_le hκ).2
    have hcard : κ * J.card ≤ (D h).ncard := by
      simpa only [J, ← Set.ncard_eq_toFinset_card'] using hGcard
    simpa only [Nat.mul_comm] using hcard
  have hν : ∀ i, activation h ≤ ν i ∧ ν i ≤ 0 := by
    intro i
    have hτi := hτ i.val (Set.mem_toFinset.mp i.property)
    have hhor := activation_add_horizon h
    dsimp [ν]
    constructor <;> omega
  have hX : nominalPath M hE κ D C h = generatedPath M (guardedPath M hE κ D C h)
      (fun i : J => i.val) ν := by
    funext k
    rw [hgen k]
    unfold generatedPath
    congr 1
    congr 1
    ext e
    constructor
    · rintro ⟨he, ht⟩
      exact ⟨⟨e, Set.mem_toFinset.mpr he⟩, ht, rfl⟩
    · rintro ⟨i, ht, rfl⟩
      exact ⟨Set.mem_toFinset.mp i.property, ht⟩
  rw [hX] at hz ⊢
  apply integerResidual_mem_family M hE U J Z q
    (guardedPath M hE κ D C h) (guardedPath_mono M hE κ D C h)
    (activation h) (by unfold activation; omega) _
    (fun k hk => guardedPath_nonnegative M hE κ D C h hk) ε K hK ν hν β hz test hnonloop hJ hJcard hZU hZcard
  intro k hk
  apply guardedPath_early M hE κ D C h
  unfold activation at hk
  omega

lemma exists_captured_residualQ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h : ℕ) (U : Finset α) (O I : Set α)
    (hDU : D h ⊆ (U : Set α)) (hI : I ⊆ D h)
    (hnonloop : ∀ e ∈ U, e ∉ M.closure ∅) (ε : Fin 2)
    (q : ℕ) (hDq : (D h).ncard / κ ≤ q)
    (hzsmall : nominalRankStatistic M hE κ D C T h (U : Set α) O ε ≤ q) :
    ∃ R ∈ labeledResidualFamilyQ M U q (guardedPath M hE κ D C h) (activation h) ε
        (fun b => lowerCompetition M hE κ D C T b.val.val h),
      (R : Set α) ⊆ O ∧ safeLayerStatistic M hE κ D C T h (U : Set α) I ε ≤
        κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
  classical
  obtain ⟨W, hW, hsum, hspan, Z, hZU, hZcard, β, hβ⟩ :=
    nominal_rank_witnesses M hE κ D C T h U O ε
  let R := (Set.toFinite (nominalResidualSet M hE κ D C T h (U : Set α) ε W)).toFinset
  have hmask : (R : Set α) ⊆ O := by
    intro e he
    exact residualUnion_subset_mask M _ _ W O hspan ((Set.Finite.mem_toFinset _).mp he)
  have hdet : safeLayerStatistic M hE κ D C T h (U : Set α) I ε ≤
      κ * nominalRankStatistic M hE κ D C T h (U : Set α) O ε + R.card := by
    have h := safeStatistic_le_witness_residual M hE κ D C T h (U : Set α) I hI ε W
    rwa [hsum, Set.ncard_eq_toFinset_card] at h
  refine ⟨R, ?_, hmask, hdet⟩
  apply Finset.mem_image.mpr
  refine ⟨integerResidual M (nominalPath M hE κ D C h) (groupLabel U) (activation h) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h) (fun w : Z => w.val) β, ?_, ?_⟩
  · apply nominal_residual_mem_familyQ M hE κ hκ D C h U Z hDU hZU q hDq (hZcard.trans hzsmall) ε
      (fun b => lowerCompetition M hE κ D C T b.val.val h)
      (fun b => lowerCompetition_subset_guarded M hE κ D C T b.val.val h) β
    · intro w
      have hw : w.val ∈ W (β w) := by
        rw [← hβ (β w)]
        exact ⟨w, rfl, rfl⟩
      exact (hW (β w) hw).1.2.2.2.1
    · exact fun i => hnonloop _ (groupLabel_mem U i)
  · exact nominalResidualSet_eq_labeled M hE κ D C T h U Z ε W β hβ


lemma safeLayerStatistic_le_sample
    {α : Type u_1} [Fintype α] [LinearOrder α] (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U I : Set α) (ε : Fin 2) :
    safeLayerStatistic M hE κ D C T h U I ε ≤ I.ncard := by
  let L := safeLayerSet M hE κ D C T h U I ε
  have hd : Pairwise (fun b c => Disjoint (L b) (L c)) := by
    intro b c hbc
    exact (nominalLayerSet_disjoint M hE κ D C h U ε hbc).mono
      (fun _ he => he.1.2) (fun _ he => he.1.2)
  have heq : (⋃ b, L b).ncard = ∑ b, (L b).ncard := by
    simpa only [finsum_eq_sum_of_fintype] using
      Set.ncard_iUnion_of_finite (fun b => Set.toFinite (L b)) hd
  rw [show safeLayerStatistic M hE κ D C T h U I ε = ∑ b, (L b).ncard from rfl, ← heq]
  apply Set.ncard_le_ncard _ (Set.toFinite I)
  intro e he
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp he
  exact hb.1.1

/-- The largest member of a family contained in `S`. -/
noncomputable def capturedMax {β : Type*} (F : Finset (Finset β)) (S : Finset β) : ℕ := by
  classical
  exact (F.filter (fun R => R ⊆ S)).sup Finset.card

lemma card_le_capturedMax {β : Type*} (F : Finset (Finset β)) (S R : Finset β) (hR : R ∈ F)
    (hRS : R ⊆ S) : R.card ≤ capturedMax F S := by
  classical
  unfold capturedMax
  convert Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨hR, hRS⟩ : R ∈ F.filter (fun R => R ⊆ S))

/-- Transfer gap with a capped generator budget: the largest captured residual, plus the whole
group on the event that the density sample exceeds the cap. -/
lemma nominalTransferGap_le_capped (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h : ℕ) (U S : Finset α) (O I : Set α)
    (hDU : D h ⊆ (U : Set α)) (hI : I ⊆ D h) (hS : S ⊆ U)
    (hOS : O ∩ (U : Set α) ⊆ (S : Set α))
    (hnonloop : ∀ e ∈ U, e ∉ M.closure ∅) (ε : Fin 2) (q : ℕ) :
    nominalTransferGap M hE κ D C T h (U : Set α) O I ε ≤
      (capturedMax (labeledResidualFamilyQ M U q (guardedPath M hE κ D C h) (activation h) ε
          (fun b => lowerCompetition M hE κ D C T b.val.val h)) S : ℝ) +
        (U.card : ℝ) * (if q < (D h).ncard / κ then 1 else 0) := by
  classical
  set F := labeledResidualFamilyQ M U q (guardedPath M hE κ D C h) (activation h) ε
    (fun b => lowerCompetition M hE κ D C T b.val.val h)
  set z := nominalRankStatistic M hE κ D C T h (U : Set α) O ε
  set σ := safeLayerStatistic M hE κ D C T h (U : Set α) I ε
  have hcap0 : (0 : ℝ) ≤ capturedMax F S := Nat.cast_nonneg _
  have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have hσU : (σ : ℝ) ≤ U.card := by
    have hs := safeLayerStatistic_le_ncard M hE κ D C T h (U : Set α) I ε
    rw [Set.ncard_coe_finset] at hs
    exact_mod_cast hs
  by_cases hq : (D h).ncard / κ ≤ q
  · have hind : (if q < (D h).ncard / κ then (1 : ℝ) else 0) = 0 := by
      rw [ite_eq_right_iff]; intro h'; omega
    rw [hind, mul_zero, add_zero]
    by_cases hz : z ≤ (D h).ncard / κ
    · obtain ⟨R, hR, hRO, hdet⟩ := exists_captured_residualQ M hE κ hκ D C T h U O I
        hDU hI hnonloop ε q hq (hz.trans hq)
      have hRU : R ⊆ U := labeledResidualFamilyQ_subsets M U q _ _ ε _ R hR
      have hRS : R ⊆ S := fun e he => hOS ⟨hRO he, hRU he⟩
      have hcap : (R.card : ℝ) ≤ capturedMax F S := by
        exact_mod_cast card_le_capturedMax F S R hR hRS
      have hdet' : (σ : ℝ) ≤ (κ : ℝ) * z + R.card := by exact_mod_cast hdet
      exact max_le (by linarith) hcap0
    · have hlt : (D h).ncard < κ * z := by
        have h1 : (D h).ncard / κ + 1 ≤ z := by omega
        have h2 := Nat.lt_mul_div_succ (D h).ncard hκ
        calc (D h).ncard < κ * ((D h).ncard / κ + 1) := h2
          _ ≤ κ * z := Nat.mul_le_mul_left κ h1
      have hσD : σ ≤ (D h).ncard := (safeLayerStatistic_le_sample M hE κ D C T h _ I ε).trans
        (Set.ncard_le_ncard hI (Set.toFinite _))
      have hσz : (σ : ℝ) ≤ (κ : ℝ) * z := by exact_mod_cast (hσD.trans hlt.le)
      exact max_le (by linarith) hcap0
  · have hind : (if q < (D h).ncard / κ then (1 : ℝ) else 0) = 1 := by
      rw [ite_eq_left_iff]; intro h'; omega
    rw [hind, mul_one]
    have hz0 : (0 : ℝ) ≤ (κ : ℝ) * z := by positivity
    exact max_le (by linarith) (by linarith)

end MatroidProphet

end OAI
