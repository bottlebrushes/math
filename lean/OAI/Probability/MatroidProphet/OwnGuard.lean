import OAI.Probability.MatroidProphet.RankCost
import OAI.Probability.MatroidProphet.CommonBudget

/-!
# Own guards cost only at the opposite parity

The final path of a group `h` adds its own guards `C h ∩ X_h(k+1)` at time `k`.  A layer
`(b-2, b]` sees them in its base `F̂(b-2)` only if they were born at `b - 1`, which has the
opposite parity.  Summed over both parities the own-guard cost is at most `|C h|`, so the
fair parity halves it.  Later groups' guards and density generators are charged as before.
-/

namespace OAI

namespace MatroidProphet
open Set Finset

variable {α : Type*} [Fintype α]

/-- Generators of all later groups' guards and density expansions. -/
def higherPathGenerators (C J : ℕ → Set α) (h : ℕ) : ℕ → Set α
  | 0 => ∅
  | t+1 => higherPathGenerators C J h t ∪ C (h+1+t) ∪ J (h+1+t)

omit [Fintype α] in
lemma higherPathGenerators_cost (κ : ℕ) (C D J : ℕ → Set α) (h t : ℕ)
    (hJ : ∀ j, κ * (J j).ncard ≤ (D j).ncard) :
    κ * (higherPathGenerators C J h t).ncard ≤
      ∑ j ∈ range t, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  induction t with
  | zero => simp [higherPathGenerators]
  | succ t ih =>
    have hcard := ncard_union_le (higherPathGenerators C J h t ∪ C (h+1+t)) (J (h+1+t))
    have hcard' := ncard_union_le (higherPathGenerators C J h t) (C (h+1+t))
    have hc : (higherPathGenerators C J h (t+1)).ncard ≤
        (higherPathGenerators C J h t).ncard + (C (h+1+t)).ncard + (J (h+1+t)).ncard :=
      hcard.trans (Nat.add_le_add_right hcard' _)
    have hm := Nat.mul_le_mul_left κ hc
    simp only [Nat.mul_add] at hm
    rw [sum_range_succ]
    have hj := hJ (h+1+t)
    omega

lemma higherPathGenerators_spans (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C J : ℕ → Set α) (h t : ℕ)
    (hJ : ∀ j k, nominalPath M hE κ D C j k ⊆
      M.closure (guardedPath M hE κ D C j k ∪ J j)) (k : ℤ) :
    guardedPath M hE κ D C (h+1+t) k ⊆
      M.closure (guardedPath M hE κ D C (h+1) k ∪ higherPathGenerators C J h t) := by
  induction t with
  | zero =>
    simp only [Nat.add_zero, higherPathGenerators, union_empty]
    exact M.subset_closure _ (by simp [hE])
  | succ t ih =>
    have hidx : h+1+(t+1) = (h+1+t)+1 := by omega
    rw [hidx, guardedPath_succ]
    apply M.closure_subset_closure_of_subset_closure
    apply Set.union_subset
    · apply (hJ (h+1+t) k).trans
      apply M.closure_subset_closure_of_subset_closure
      apply Set.union_subset
      · exact ih.trans (M.closure_subset_closure (by
          intro e he
          rcases he with he | he
          · exact Or.inl he
          · exact Or.inr (Or.inl (Or.inl he))))
      · intro e he
        exact M.mem_closure_of_mem (Or.inr (Or.inr he)) (by simp [hE])
    · intro e he
      exact M.mem_closure_of_mem (Or.inr (Or.inl (Or.inr he.1))) (by simp [hE])

theorem exists_higherPathBudget (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h t : ℕ) :
    ∃ J : Set α,
      κ * J.ncard ≤ ∑ j ∈ range t, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) ∧
      ∀ k, guardedPath M hE κ D C (h+1+t) k ⊆
        M.closure (guardedPath M hE κ D C (h+1) k ∪ J) := by
  choose J hJD hcard τ htime hgen using
    (fun j => nominalPath_all_time_generators M hE κ hκ D C j)
  refine ⟨higherPathGenerators C J h t, higherPathGenerators_cost κ C D J h t hcard, ?_⟩
  intro k
  apply higherPathGenerators_spans M hE κ D C J h t _ k
  intro j l
  rw [hgen j l]
  apply M.closure_subset_closure
  exact union_subset_union_right _ (fun _ he => he.1)

/-- Own guards entering the base of layer `(b-2, b]`. -/
def ownGuards (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ) (D C : ℕ → Set α) (h : ℕ)
    (b : ℤ) : Set α :=
  C h ∩ (nominalPath M hE κ D C h (b-1) \ nominalPath M hE κ D C h (b-2))

/-- Adding the group's own guards costs at most the guards born just before the layer. -/
lemma ownGuard_step (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ) (D C : ℕ → Set α)
    (h : ℕ) (b : ℤ) (S K : Set α) :
    conditionalRank M S (nominalPath M hE κ D C h (b-2) ∪ K) ≤
      conditionalRank M S (guardedPath M hE κ D C (h+1) (b-2) ∪ K) +
        (ownGuards M hE κ D C h b).ncard := by
  set A := nominalPath M hE κ D C h (b-2) ∪ K
  set G := ownGuards M hE κ D C h b
  have hex := conditionalRank_exchange M S G A
  have hG := (conditionalRank_le_rank M G A).trans (natRank_le_ncard M G)
  have hsub : guardedPath M hE κ D C (h+1) (b-2) ∪ K ⊆ M.closure (A ∪ G) := by
    rw [guardedPath_succ]
    apply Set.union_subset
    · apply M.closure_subset_closure_of_subset_closure
      apply Set.union_subset
      · exact fun e he => M.mem_closure_of_mem (Or.inl (Or.inl he)) (by simp [hE])
      · intro e he
        by_cases hx : e ∈ nominalPath M hE κ D C h (b-2)
        · exact M.mem_closure_of_mem (Or.inl (Or.inl hx)) (by simp [hE])
        · have hb : (b-2)+1 = b-1 := by ring
          rw [hb] at he
          exact M.mem_closure_of_mem (Or.inr ⟨he.1, he.2, hx⟩) (by simp [hE])
    · exact fun e he => M.mem_closure_of_mem (Or.inl (Or.inr he)) (by simp [hE])
  have hanti := conditionalRank_antitone M S hsub
  rw [conditionalRank_closure] at hanti
  omega

/-- Rank cost of passing from the nominal to the final path, with the own-guard term restricted
to guards born just before each layer. -/
theorem actual_path_rank_cost_own (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later : ℕ)
    (L : Finset ℤ) (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hlo : ∀ b ∈ L, lo+2 ≤ b) (hhi : ∀ b ∈ L, b ≤ hi)
    (hgap : ∀ b ∈ L, ∀ c ∈ L, b < c → b+2 ≤ c)
    (S : ℤ → Set α) (hS : ∀ b, S b ⊆ nominalPath M hE κ D C h b) :
    κ * (∑ b ∈ L, conditionalRank M (S b)
      (nominalPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h)) ≤
    κ * (∑ b ∈ L, conditionalRank M (S b)
      (guardedPath M hE κ D C (h+1+later) (b-2) ∪ lowerCompetition M hE κ D C T b h)) +
      κ * (∑ b ∈ L, (ownGuards M hE κ D C h b).ncard) +
        ∑ j ∈ range later, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  obtain ⟨J, hJcost, hJ⟩ := exists_higherPathBudget M hE κ hκ D C h later
  have hlevel (b : ℤ) : guardedPath M hE κ D C (h+1) b ⊆
      guardedPath M hE κ D C (h+1+later) b := by
    have hm : Monotone (fun j => guardedPath M hE κ D C j b) :=
      monotone_nat_of_le_succ (fun j => (guarded_subset_nominal M hE κ D C j b).trans
        (nominal_subset_guarded M hE κ D C j b))
    exact hm (by omega)
  have hown : (∑ b ∈ L, conditionalRank M (S b)
      (nominalPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h)) ≤
      (∑ b ∈ L, conditionalRank M (S b)
        (guardedPath M hE κ D C (h+1) (b-2) ∪ lowerCompetition M hE κ D C T b h)) +
        ∑ b ∈ L, (ownGuards M hE κ D C h b).ncard := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun b _ => ownGuard_step M hE κ D C h b _ _
  have hr := rankCost_spaced M J L lo hi hlohi hlo hhi hgap
    (guardedPath M hE κ D C (h+1))
    (fun b => guardedPath M hE κ D C (h+1) (b-2) ∪ lowerCompetition M hE κ D C T b h)
    (fun b => guardedPath M hE κ D C (h+1+later) (b-2) ∪ lowerCompetition M hE κ D C T b h)
    S (guardedPath_mono M hE κ D C (h+1))
    (fun _ _ => Set.subset_union_left)
    (fun b _ => Set.union_subset_union_left _ (hlevel _))
    (by
      intro b hb
      apply Set.union_subset
      · exact (hJ _).trans (M.closure_subset_closure (by
          intro e he
          rcases he with he | he
          · exact Or.inl (Or.inl he)
          · exact Or.inr he))
      · intro e he
        exact M.mem_closure_of_mem (Or.inl (Or.inr he)) (by simp [hE]))
    (by
      intro b hb
      apply Set.union_subset
      · apply Set.union_subset
        · exact guardedPath_mono M hE κ D C (h+1) (by omega)
        · exact ((lowerCompetition_subset_guarded M hE κ D C T _ h).trans
            (guarded_subset_nominal M hE κ D C h _)).trans (nominal_subset_guarded M hE κ D C h _)
      · exact (hS _).trans (nominal_subset_guarded M hE κ D C h _))
  have hmul := Nat.mul_le_mul_left κ (hown.trans (Nat.add_le_add_right hr _))
  simp only [Nat.mul_add] at hmul
  have hcard := natRank_le_ncard M J
  have hbound := (Nat.mul_le_mul_left κ hcard).trans hJcost
  omega

/-- Over both parities the own guards entering layer bases are disjoint subsets of `C h`. -/
theorem ownGuards_both_parities (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ)
    (D C : ℕ → Set α) (h : ℕ) (a : ℤ) :
    (∑ b ∈ parityPoints a 0, (ownGuards M hE κ D C h b).ncard) +
      (∑ b ∈ parityPoints a 1, (ownGuards M hE κ D C h b).ncard) ≤ (C h).ncard := by
  classical
  have hdisj : Disjoint (parityPoints a 0) (parityPoints a 1) := by
    rw [Finset.disjoint_left]
    intro b h0 h1
    have := ((mem_parityPoints _ _ _).mp h0).2.2
    have := ((mem_parityPoints _ _ _).mp h1).2.2
    simp at *; omega
  rw [← Finset.sum_union hdisj]
  set P := parityPoints a 0 ∪ parityPoints a 1
  have hpw : (P : Set ℤ).PairwiseDisjoint (fun b => (ownGuards M hE κ D C h b).toFinset) := by
    intro b _ c _ hbc
    simp only [Function.onFun]
    rw [Set.disjoint_toFinset]
    rcases lt_or_gt_of_ne hbc with hlt | hlt
    · rw [Set.disjoint_left]
      rintro e ⟨_, hb, _⟩ ⟨_, _, hc⟩
      exact hc (nominalPath_mono M hE κ D C h (by omega) hb)
    · rw [Set.disjoint_left]
      rintro e ⟨_, _, hb⟩ ⟨_, hc, _⟩
      exact hb (nominalPath_mono M hE κ D C h (by omega) hc)
  have hcard := Finset.card_biUnion hpw
  have hsub : P.biUnion (fun b => (ownGuards M hE κ D C h b).toFinset) ⊆ (C h).toFinset := by
    intro e he
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp he
    exact Set.mem_toFinset.mpr (Set.mem_toFinset.mp hb).1
  have hle := Finset.card_le_card hsub
  simp only [Set.ncard_eq_toFinset_card'] at *
  omega

end MatroidProphet

end OAI
