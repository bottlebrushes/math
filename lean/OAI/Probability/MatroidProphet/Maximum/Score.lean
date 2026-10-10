import OAI.Probability.MatroidProphet.BranchMix

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable def maximumRounded {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (fun o : Option (Fin n) =>
    match o with
    | none => 0
    | some e => if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0)

lemma maximumRounded_nonneg {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) :
    0 ≤ maximumRounded M w := by
  classical
  exact Finset.le_sup' (s := Finset.univ)
    (f := fun o : Option (Fin n) => match o with
      | none => 0
      | some e => if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0)
    (Finset.mem_univ none)

lemma roundedWeight_le_maximumRounded {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (e : Fin n) (he : M.Indep ({e} : Set (Fin n))) :
    roundedWeight weightBase (w e) ≤ maximumRounded M w := by
  classical
  have h := Finset.le_sup' (s := Finset.univ)
    (f := fun o : Option (Fin n) => match o with
      | none => 0
      | some e => if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0)
    (Finset.mem_univ (some e))
  change (if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0) ≤
    maximumRounded M w at h
  rwa [ite_eq_left he] at h

noncomputable def maximumPayoff {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) : ℝ :=
  ∫ r, hiddenWorstReward (roundedMaximumHidden M (seedSet (bits := n))) w r
    ∂bernoulliSeedLaw (fun _ => filterRate) (fun _ => rates_mem.1.le) (fun _ => rates_mem.2.1.le)

lemma maximumPayoff_nonneg {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ maximumPayoff M w :=
  integral_nonneg (fun r => hiddenWorstReward_nonneg _ w hw r)

lemma roundedWeight_le_maximumPayoff {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (hw : ∀ e, 0 ≤ w e) (e : Fin n) (he : M.Indep ({e} : Set (Fin n))) :
    maximumFactor * roundedWeight weightBase (w e) ≤ maximumPayoff M w := by
  classical
  let a : Fin n → WithBot ℤ := fun f => Priority.asLevel (roundedLevel weightBase (w f))
  by_cases hea : a e = ⊥
  · have hu : roundedWeight weightBase (w e) = 0 := by
      change levelWeight weightBase (a e) = 0
      rw [hea]
      rfl
    rw [hu, mul_zero]
    exact maximumPayoff_nonneg M w hw
  · let P : Finset (Fin n) := Finset.univ.filter fun f => M.Indep ({f} : Set (Fin n)) ∧ a f ≠ ⊥
    have heP : e ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ e, he, hea⟩
    obtain ⟨g, hgP, htop⟩ := Maximum.exists_top a P ⟨e, heP⟩
    have hg := (Finset.mem_filter.mp hgP).2
    have hwin : filterRate * (1 - filterRate) * w g ≤ maximumPayoff M w :=
      Maximum.maximum_integral_top filterRate rates_mem.1.le rates_mem.2.1.le M (fun x => Priority.asLevel (roundedLevel weightBase x))
        ((measurable_of_countable Priority.asLevel).comp (measurable_roundedLevel weightBase))
        (fun x => x ≠ ⊥) w hw g hg.1 hg.2
        (fun f hf haf hfg => htop f (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf, haf⟩) hfg)
    have hkey : a e ≤ a g := by
      by_cases heg : e = g
      · exact heg ▸ le_rfl
      · rcases htop e heP heg with hlt | ⟨heq, _⟩
        · exact hlt.le
        · exact heq.symm.le
    have hu : roundedWeight weightBase (w e) ≤ roundedWeight weightBase (w g) :=
      levelWeight_mono (by norm_num [weightBase]) hkey
    have hraw := roundedWeight_le (by norm_num [weightBase] : 1 < weightBase) (hw g)
    have hf : 0 ≤ maximumFactor := by norm_num [maximumFactor, filterRate]
    have h1 := mul_le_mul_of_nonneg_left (hu.trans hraw) hf
    unfold maximumFactor at h1 ⊢
    linarith

theorem maximum_branch_guarantee {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (hw : ∀ e, 0 ≤ w e) : maximumFactor * maximumRounded M w ≤ maximumPayoff M w := by
  classical
  have hnonneg := maximumPayoff_nonneg M w hw
  have hf : 0 < maximumFactor := by norm_num [maximumFactor, filterRate]
  have hfour : maximumRounded M w ≤ maximumPayoff M w / maximumFactor := by
    apply Finset.sup'_le
    intro o _
    cases o with
    | none => exact div_nonneg hnonneg hf.le
    | some e =>
      change (if M.Indep ({e} : Set (Fin n)) then roundedWeight weightBase (w e) else 0) ≤ _
      split_ifs with he
      · rw [le_div_iff₀ hf, mul_comm]
        exact roundedWeight_le_maximumPayoff M w hw e he
      · exact div_nonneg hnonneg hf.le
  rw [le_div_iff₀ hf] at hfour
  linarith

end MatroidProphet

end OAI
