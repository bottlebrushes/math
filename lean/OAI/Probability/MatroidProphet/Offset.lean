import OAI.Probability.MatroidProphet.Rounding
import OAI.Probability.MatroidProphet.Model
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Log

/-!
# Randomly offset rounding

Rounding to powers of `B = 2^8` loses a factor `B` in the worst case.  Running the rule on
the weights scaled by `2^{-m}`, for a uniformly random `m ∈ {0, …, 7}` drawn from three extra
fair seed bits, rounds each weight to one of eight interleaved grids.  On average the rounded
weight is at least `(1 - 1/B)/8` of the true weight.
-/

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable section

/-- Rounding at least captures every grid point below the weight. -/
lemma zpow_le_roundedWeight {B : ℝ} (hB : 1 < B) {y : ℝ} (hy : 0 < y) {i : ℤ}
    (hi : B ^ i ≤ y) : B ^ i ≤ roundedWeight B y := by
  unfold roundedWeight roundedLevel
  rw [ite_eq_left hy, levelWeight]
  apply zpow_le_zpow_right₀ hB.le
  apply Int.le_floor.mpr
  rw [Real.le_logb_iff_rpow_le hB hy, Real.rpow_intCast]
  exact hi

/-- The residues `(L - m) mod 8` of `m < 8` run over `{0, …, 7}`. -/
lemma sum_range_eight_shift (L : ℤ) (f : ℕ → ℝ) :
    (∑ m ∈ range 8, f ((L - m) % 8).toNat) = ∑ r ∈ range 8, f r := by
  apply Finset.sum_nbij' (fun m : ℕ => ((L - m) % 8).toNat) (fun r : ℕ => ((L - r) % 8).toNat)
  · intro m hm; simp only [mem_range] at hm ⊢; omega
  · intro r hr; simp only [mem_range] at hr ⊢; omega
  · intro m hm; simp only [mem_range] at hm; omega
  · intro r hr; simp only [mem_range] at hr; omega
  · intro m hm; rfl

/-- Averaged over the eight offsets, rounding to powers of `2^8` keeps `(1 - 2^{-8})/8` of
every nonnegative weight. -/
theorem offset_rounding_sum {x : ℝ} (hx : 0 ≤ x) :
    x * (1 - 1 / 2 ^ 8) ≤
      ∑ m ∈ range 8, (2 : ℝ) ^ m * roundedWeight (2 ^ 8) (x / 2 ^ m) := by
  rcases hx.lt_or_eq with hpos | hzero
  · set L := Int.log 2 x
    have hL : (2 : ℝ) ^ L ≤ x := Int.zpow_log_le_self (by norm_num) hpos
    have hL1 : x < (2 : ℝ) ^ (L + 1) := Int.lt_zpow_succ_log_self (by norm_num) x
    have hterm (m : ℕ) (hm : m < 8) :
        (2 : ℝ) ^ (L - ((L - m) % 8).toNat) ≤
          (2 : ℝ) ^ m * roundedWeight (2 ^ 8) (x / 2 ^ m) := by
      set r := ((L - m) % 8).toNat
      have hr : ((r : ℤ)) = (L - m) % 8 := by omega
      set i : ℤ := (L - m - r) / 8
      have hi : 8 * i = L - m - r := by omega
      have hpow : ((2 : ℝ) ^ 8) ^ i = (2 : ℝ) ^ (L - m - r) := by
        rw [← hi, zpow_mul]; norm_num
      have hle : ((2 : ℝ) ^ 8) ^ i ≤ x / 2 ^ m := by
        rw [hpow, le_div_iff₀ (by positivity), ← zpow_natCast, ← zpow_add₀ (by norm_num)]
        calc (2 : ℝ) ^ (L - m - r + m) ≤ 2 ^ L :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ ≤ x := hL
      have hround := zpow_le_roundedWeight (by norm_num : (1 : ℝ) < 2 ^ 8)
        (div_pos hpos (by positivity)) hle
      rw [hpow] at hround
      calc (2 : ℝ) ^ (L - r) = 2 ^ m * 2 ^ (L - m - r) := by
            rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hround (by positivity)
    have hsum := Finset.sum_le_sum (fun m hm => hterm m (mem_range.mp hm))
    rw [sum_range_eight_shift L (fun r => (2 : ℝ) ^ (L - r))] at hsum
    have hgeom : (∑ r ∈ range 8, (2 : ℝ) ^ (L - r)) = 2 ^ (L + 1) * (1 - 1 / 2 ^ 8) := by
      have h (r : ℕ) : (2 : ℝ) ^ (L - r) = 2 ^ (L + 1) * (1 / 2 ^ (r + 1)) := by
        rw [one_div, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (by norm_num)]
        congr 1; push_cast; ring
      simp only [h, ← Finset.mul_sum]
      congr 1
      norm_num [Finset.sum_range_succ]
    have hc : (0 : ℝ) ≤ 1 - 1 / 2 ^ 8 := by norm_num
    calc x * (1 - 1 / 2 ^ 8) ≤ 2 ^ (L + 1) * (1 - 1 / 2 ^ 8) :=
          mul_le_mul_of_nonneg_right hL1.le hc
      _ ≤ _ := hgeom ▸ hsum
  · subst hzero
    simp only [zero_mul]
    exact Finset.sum_nonneg (fun m _ =>
      mul_nonneg (by positivity) (roundedWeight_nonneg (by norm_num) _))

/-- Every optimum is attained by an independent set. -/
lemma exists_optimal_indep {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) :
    ∃ I : Finset (Fin n), M.Indep (I : Set (Fin n)) ∧ optimum M w ≤ ∑ e ∈ I, w e := by
  classical
  obtain ⟨I, -, hI⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Finset (Fin n))))
    Finset.univ_nonempty
    (fun I : Finset (Fin n) => if M.Indep (I : Set (Fin n)) then ∑ e ∈ I, w e else 0)
  have hopt : optimum M w = if M.Indep (I : Set (Fin n)) then ∑ e ∈ I, w e else 0 := by
    unfold optimum; convert hI
  by_cases hi : M.Indep (I : Set (Fin n))
  · exact ⟨I, hi, by rw [hopt, ite_eq_left hi]⟩
  · exact ⟨∅, by simp, by rw [hopt, ite_eq_right hi]; simp⟩

/-- The offset index `m ∈ {0, …, 7}` encoded by three seed bits. -/
def offsetIndex (j : Seed 3) : ℕ :=
  (if j 0 then 1 else 0) + (if j 1 then 2 else 0) + (if j 2 then 4 else 0)

lemma sum_offsetIndex (h : ℕ → ℝ) :
    (∑ j : Seed 3, h (offsetIndex j)) = ∑ m ∈ range 8, h m := by
  apply Finset.sum_nbij' (fun j => offsetIndex j) (fun m : ℕ => fun i : Fin 3 => m.testBit i)
  · intro j _; simp only [mem_range, offsetIndex]; split_ifs <;> omega
  · intro m _; exact mem_univ _
  · intro j _; revert j; decide
  · intro m hm
    simp only [mem_range] at hm
    revert m; decide
  · intro j _; rfl

/-- Scale factor `2^{-m}` applied to the weights. -/
def offsetScale (j : Seed 3) : ℝ := ((2 : ℝ) ^ offsetIndex j)⁻¹

lemma offsetScale_pos (j : Seed 3) : 0 < offsetScale j := by
  unfold offsetScale; positivity

/-- Split a seed into the base seed and the three offset bits. -/
def baseSeed {bits : ℕ} (r : Seed (bits + 3)) : Seed bits := fun i => r (Fin.castAdd 3 i)

def offsetSeed {bits : ℕ} (r : Seed (bits + 3)) : Seed 3 := fun i => r (Fin.natAdd bits i)

/-- Scale the values of an arrival history. -/
def scaleHistory {n : ℕ} {k : Fin n} (c : ℝ) (hist : History n k) : History n k :=
  fun j => ((hist j).1, c * (hist j).2)

lemma history_smul {n : ℕ} (c : ℝ) (v : Weights n) (π : ArrivalOrder n) (k : Fin n) :
    history (fun e => c * v e) π k = scaleHistory c (history v π k) := rfl

/-- Run the online rule on weights scaled by the seed's offset. -/
def offsetOnlineRule {n bits : ℕ} (A : OnlineRule n bits) : OnlineRule n (bits + 3) where
  decide k r s hist := A.decide k (baseSeed r) (fun e => offsetScale (offsetSeed r) * s e)
    (scaleHistory (offsetScale (offsetSeed r)) hist)
  measurable_decide k := by
    have hc : Measurable (fun x : Seed (bits + 3) × (Weights n × History n k) =>
        offsetScale (offsetSeed x.1)) :=
      (measurable_of_countable (fun r : Seed (bits + 3) => offsetScale (offsetSeed r))).comp
        measurable_fst
    have hb : Measurable (fun x : Seed (bits + 3) × (Weights n × History n k) =>
        baseSeed x.1) :=
      (measurable_of_countable (fun r : Seed (bits + 3) => baseSeed r)).comp measurable_fst
    have hs : Measurable (fun x : Seed (bits + 3) × (Weights n × History n k) =>
        fun e => offsetScale (offsetSeed x.1) * x.2.1 e) := by
      apply measurable_pi_lambda
      intro e
      exact hc.mul ((measurable_pi_apply e).comp (measurable_fst.comp measurable_snd))
    have hh : Measurable (fun x : Seed (bits + 3) × (Weights n × History n k) =>
        scaleHistory (offsetScale (offsetSeed x.1)) x.2.2) := by
      apply measurable_pi_lambda
      intro j
      have hj : Measurable (fun x : Seed (bits + 3) × (Weights n × History n k) => x.2.2 j) :=
        (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
      exact (measurable_fst.comp hj).prodMk (hc.mul (measurable_snd.comp hj))
    exact (A.measurable_decide k).comp (hb.prodMk (hs.prodMk hh))

/-- The hidden rule with a random rounding offset. -/
def offsetHiddenRule {n bits : ℕ} (A : HiddenRule n bits) : HiddenRule n (bits + 3) where
  mask r := A.mask (baseSeed r)
  core := offsetOnlineRule A.core

lemma offsetHiddenRule_decide {n bits : ℕ} (A : HiddenRule n bits) (k : Fin n)
    (r : Seed (bits + 3)) (s : Weights n) (hist : History n k) :
    (offsetHiddenRule A).core.decide k r s hist =
      A.core.decide k (baseSeed r) (fun e => offsetScale (offsetSeed r) * s e)
        (scaleHistory (offsetScale (offsetSeed r)) hist) := rfl

lemma offsetHiddenRule_mask {n bits : ℕ} (A : HiddenRule n bits) (r : Seed (bits + 3)) :
    (offsetHiddenRule A).mask r = A.mask (baseSeed r) := rfl

lemma offset_hiddenAcceptedThrough {n bits : ℕ} (A : HiddenRule n bits) (r : Seed (bits + 3))
    (w : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    hiddenAcceptedThrough (offsetHiddenRule A) r w π t =
      hiddenAcceptedThrough A (baseSeed r) (fun e => offsetScale (offsetSeed r) * w e) π t := by
  classical
  have hobs : (fun e => offsetScale (offsetSeed r) * observed (offsetHiddenRule A) r w e) =
      observed A (baseSeed r) (fun e => offsetScale (offsetSeed r) * w e) := by
    funext e
    by_cases h : e ∈ A.mask (baseSeed r) <;>
      simp [observed, offsetHiddenRule_mask, h]
  have hdec (k : Fin n) :
      decisionAt (offsetHiddenRule A).core r (observed (offsetHiddenRule A) r w) w π k =
        decisionAt A.core (baseSeed r)
          (observed A (baseSeed r) (fun e => offsetScale (offsetSeed r) * w e))
          (fun e => offsetScale (offsetSeed r) * w e) π k := by
    simp only [decisionAt]
    rw [offsetHiddenRule_decide, hobs, ← history_smul]
  simp only [hiddenAcceptedThrough, acceptedThrough, hdec, offsetHiddenRule_mask]

lemma offset_hiddenWorstReward {n bits : ℕ} (A : HiddenRule n bits) (r : Seed (bits + 3))
    (w : Weights n) :
    (offsetScale (offsetSeed r))⁻¹ *
        hiddenWorstReward A (fun e => offsetScale (offsetSeed r) * w e) (baseSeed r) ≤
      hiddenWorstReward (offsetHiddenRule A) w r := by
  classical
  set c := offsetScale (offsetSeed r)
  have hc := offsetScale_pos (offsetSeed r)
  unfold hiddenWorstReward
  apply Finset.le_inf'
  intro π _
  have hreward : hiddenReward (offsetHiddenRule A) r w π =
      c⁻¹ * hiddenReward A (baseSeed r) (fun e => c * w e) π := by
    unfold hiddenReward
    rw [offset_hiddenAcceptedThrough, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  rw [hreward]
  exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (mem_univ π)) (inv_pos.mpr hc).le

lemma offsetHiddenRule_feasible {n bits : ℕ} (M : Matroid (Fin n)) (A : HiddenRule n bits)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) → ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
      M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n))) :
    ∀ (w : Weights n), (∀ e, 0 ≤ w e) → ∀ (r : Seed (bits + 3)) (π : ArrivalOrder n) (t : ℕ),
      M.Indep (hiddenAcceptedThrough (offsetHiddenRule A) r w π t : Set (Fin n)) := by
  intro w hw r π t
  rw [offset_hiddenAcceptedThrough]
  exact hA _ (fun e => mul_nonneg (offsetScale_pos _).le (hw e)) _ π t

/-- Seed law: the base law together with three independent fair bits. -/
def offsetSeedLaw {bits : ℕ} (ν : Measure (Seed bits)) : Measure (Seed (bits + 3)) :=
  (ν.prod (PMF.uniformOfFintype (Seed 3)).toMeasure).map (fun p => Fin.append p.1 p.2)

instance offsetSeedLaw_probability {bits : ℕ} (ν : Measure (Seed bits))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (offsetSeedLaw ν) := by
  unfold offsetSeedLaw
  infer_instance

lemma baseSeed_append {bits : ℕ} (a : Seed bits) (j : Seed 3) :
    baseSeed (Fin.append a j) = a := by
  funext i; simp [baseSeed]

lemma offsetSeed_append {bits : ℕ} (a : Seed bits) (j : Seed 3) :
    offsetSeed (Fin.append a j) = j := by
  funext i; simp [offsetSeed]

lemma integral_offsetSeedLaw {bits : ℕ} (ν : Measure (Seed bits)) [IsProbabilityMeasure ν]
    (f : Seed (bits + 3) → ℝ) :
    (∫ r, f r ∂offsetSeedLaw ν) =
      ∫ a, (1 / 8 : ℝ) * ∑ j : Seed 3, f (Fin.append a j) ∂ν := by
  unfold offsetSeedLaw
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  rw [integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  refine ae_of_all _ fun a => ?_
  dsimp only
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp

/-- Offset rounding: a guarantee against the rounded optimum becomes one against the true
optimum, losing only `(1 - 2^{-8})/8` instead of `2^{-8}`. -/
theorem offset_guarantee {n bits : ℕ} (M : Matroid (Fin n)) (A : HiddenRule n bits)
    (ν : Measure (Seed bits)) [IsProbabilityMeasure ν] (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      c * optimum M (fun e => roundedWeight (2 ^ 8) (w e)) ≤
        ∫ r, hiddenWorstReward A w r ∂ν)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    c * ((1 - 1 / 2 ^ 8) / 8) * optimum M w ≤
      ∫ r, hiddenWorstReward (offsetHiddenRule A) w r ∂offsetSeedLaw ν := by
  classical
  rw [integral_offsetSeedLaw]
  have hpoint (a : Seed bits) (j : Seed 3) :
      (offsetScale j)⁻¹ * hiddenWorstReward A (fun e => offsetScale j * w e) a ≤
        hiddenWorstReward (offsetHiddenRule A) w (Fin.append a j) := by
    have h := offset_hiddenWorstReward A (Fin.append a j) w
    rwa [baseSeed_append, offsetSeed_append] at h
  have hmono : (∫ a, (1 / 8 : ℝ) * ∑ j : Seed 3,
        (offsetScale j)⁻¹ * hiddenWorstReward A (fun e => offsetScale j * w e) a ∂ν) ≤
      ∫ a, (1 / 8 : ℝ) * ∑ j : Seed 3,
        hiddenWorstReward (offsetHiddenRule A) w (Fin.append a j) ∂ν := by
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro a
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hpoint a j) (by norm_num)
  refine le_trans ?_ hmono
  obtain ⟨I, hI, hopt⟩ := exists_optimal_indep M w
  have hscaled (j : Seed 3) : ∀ e, 0 ≤ offsetScale j * w e :=
    fun e => mul_nonneg (offsetScale_pos j).le (hw e)
  have hround (j : Seed 3) :
      c * ∑ e ∈ I, roundedWeight (2 ^ 8) (offsetScale j * w e) ≤
        ∫ a, hiddenWorstReward A (fun e => offsetScale j * w e) a ∂ν :=
    le_trans (mul_le_mul_of_nonneg_left (sum_le_optimum M _ I hI) hc) (hA _ (hscaled j))
  have hinv (j : Seed 3) : (offsetScale j)⁻¹ = 2 ^ offsetIndex j := by
    simp [offsetScale]
  have hdiv (j : Seed 3) (x : ℝ) : offsetScale j * x = x / 2 ^ offsetIndex j := by
    simp [offsetScale, div_eq_inv_mul]
  calc c * ((1 - 1 / 2 ^ 8) / 8) * optimum M w
      ≤ c * ((1 - 1 / 2 ^ 8) / 8) * ∑ e ∈ I, w e :=
        mul_le_mul_of_nonneg_left hopt (mul_nonneg hc (by norm_num))
    _ = (1 / 8 : ℝ) * c * ∑ e ∈ I, w e * (1 - 1 / 2 ^ 8) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ (1 / 8 : ℝ) * c * ∑ e ∈ I, ∑ m ∈ range 8,
          (2 : ℝ) ^ m * roundedWeight (2 ^ 8) (w e / 2 ^ m) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun e _ => offset_rounding_sum (hw e)
    _ = (1 / 8 : ℝ) * ∑ j : Seed 3, (offsetScale j)⁻¹ *
          (c * ∑ e ∈ I, roundedWeight (2 ^ 8) (offsetScale j * w e)) := by
        rw [Finset.sum_comm]
        simp_rw [← sum_offsetIndex, hinv, hdiv, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro e _
        ring
    _ ≤ (1 / 8 : ℝ) * ∑ j : Seed 3, (offsetScale j)⁻¹ *
          ∫ a, hiddenWorstReward A (fun e => offsetScale j * w e) a ∂ν := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hround j) (inv_pos.mpr (offsetScale_pos j)).le
    _ = _ := by
        rw [integral_const_mul, integral_finset_sum _ (fun j _ => Integrable.of_finite)]
        congr 1
        apply Finset.sum_congr rfl; intro j _
        rw [integral_const_mul]

end

end MatroidProphet

end OAI
