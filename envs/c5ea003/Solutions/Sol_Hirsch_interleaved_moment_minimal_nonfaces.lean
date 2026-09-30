-- Prove2me | solution 1 for Hirsch.interleaved_moment_minimal_nonfaces
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-17T03:12:26.800042+00:00
-- url     : https://prove2.me/submissions/3ba6a352-2bf8-4865-b809-79f945073a7c

import Mathlib

open scoped BigOperators
set_option maxHeartbeats 2000000


/-! Reused accepted namespace Hirsch.MomentSmallFaces; body unchanged. -/

namespace Hirsch.MomentSmallFaces

noncomputable def squareRoots {ι : Type*} (a : ι → ℝ) (S : Finset ι) :
    Polynomial ℝ := ∏ s ∈ S, (Polynomial.X - Polynomial.C (a s)) ^ 2

lemma eval_squareRoots {ι : Type*} (a : ι → ℝ) (S : Finset ι) (t : ℝ) :
    (squareRoots a S).eval t = ∏ s ∈ S, (t - a s) ^ 2 := by
  classical
  simp [squareRoots, Polynomial.eval_prod]

lemma squareRoots_nonneg {ι : Type*} (a : ι → ℝ) (S : Finset ι) (t : ℝ) :
    0 ≤ (squareRoots a S).eval t := by
  rw [eval_squareRoots]
  exact Finset.prod_nonneg (fun s _ => sq_nonneg (t - a s))

lemma squareRoots_zero_iff {ι : Type*} (a : ι → ℝ)
    (ha : Function.Injective a) (S : Finset ι) (i : ι) :
    (squareRoots a S).eval (a i) = 0 ↔ i ∈ S := by
  classical
  rw [eval_squareRoots]
  constructor
  · intro h
    obtain ⟨s, hs, hz⟩ := Finset.prod_eq_zero_iff.mp h
    have he : a i = a s := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    rw [ha he]
    exact hs
  · intro hi
    exact Finset.prod_eq_zero_iff.mpr ⟨i, hi, by simp⟩

lemma squareRoots_degree {ι : Type*} (a : ι → ℝ) (S : Finset ι) :
    (squareRoots a S).natDegree = 2 * S.card := by
  classical
  change (∏ s ∈ S, ((Polynomial.X : Polynomial ℝ) - Polynomial.C (a s)) ^ 2).natDegree =
    2 * S.card
  rw [Polynomial.natDegree_prod_of_monic S
    (fun s : ι => ((Polynomial.X : Polynomial ℝ) - Polynomial.C (a s)) ^ 2)
    (fun s _ => (Polynomial.monic_X_sub_C (a s)).pow 2)]
  simp [Polynomial.natDegree_pow, Nat.mul_comm]

/-- The constant coefficient is separated before centering the moment rows. -/
lemma eval_split (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n) (t : ℝ) :
    p.eval t = p.coeff 0 + ∑ j : Fin n, p.coeff (j.val + 1) * t ^ (j.val + 1) := by
  calc
    p.eval t = ∑ j ∈ Finset.range (n + 1), p.coeff j * t ^ j :=
      Polynomial.eval_eq_sum_range' (by omega) t
    _ = ∑ j : Fin (n + 1), p.coeff j.val * t ^ j.val := Finset.sum_range _
    _ = p.coeff 0 + ∑ j : Fin n, p.coeff (j.val + 1) * t ^ (j.val + 1) := by
      simpa using (Fin.sum_univ_succ
        (fun j : Fin (n + 1) => p.coeff j.val * t ^ j.val))

/-- Averaging evaluations is the same as evaluating the coefficient functional
on the averaged moment vector. No extremal-point or support oracle is used. -/
lemma average_split {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n)
    (hm : (Fintype.card ι : ℝ) ≠ 0) :
    (∑ i, p.eval (a i)) / (Fintype.card ι : ℝ) =
      p.coeff 0 + ∑ j : Fin n, p.coeff (j.val + 1) *
        ((∑ i, a i ^ (j.val + 1)) / (Fintype.card ι : ℝ)) := by
  classical
  have hexpand : (∑ i, p.eval (a i)) =
      (Fintype.card ι : ℝ) * p.coeff 0 +
        ∑ j : Fin n, p.coeff (j.val + 1) * (∑ i, a i ^ (j.val + 1)) := by
    simp_rw [eval_split p n hp]
    rw [Finset.sum_add_distrib]
    congr 1
    · simp
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact (Finset.mul_sum _ _ _).symm
  rw [hexpand, add_div, Finset.sum_div]
  congr 1
  · field_simp [hm]
  · apply Finset.sum_congr rfl
    intro j _
    ring

lemma centered_eval {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n)
    (hm : (Fintype.card ι : ℝ) ≠ 0) (i : ι) :
    (∑ j : Fin n,
      (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) *
        p.coeff (j.val + 1)) =
      p.eval (a i) - (∑ l, p.eval (a l)) / (Fintype.card ι : ℝ) := by
  classical
  have he := eval_split p n hp (a i)
  have hav := average_split a p n hp hm
  calc
    (∑ j : Fin n,
      (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) *
        p.coeff (j.val + 1)) =
      (∑ j : Fin n, p.coeff (j.val + 1) * a i ^ (j.val + 1)) -
      ∑ j : Fin n, p.coeff (j.val + 1) *
        ((∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = p.eval (a i) - (∑ l, p.eval (a l)) / (Fintype.card ι : ℝ) := by
      linarith

/-- Construct the exact original-H slack witness for every small selected set
of distinct moment parameters. All unselected inequalities are strictly slack. -/
theorem exact_small_face_witness {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : Function.Injective a) (k : ℕ) (S : Finset ι)
    (hS : S.card ≤ k) (hproper : S.card < Fintype.card ι) :
    ∃ h : ℝ, 0 < h ∧
      h = (∑ i, ∏ s ∈ S, (a i - a s) ^ 2) / (Fintype.card ι : ℝ) ∧
      ∃ x : Fin (2 * k) → ℝ, ∀ i : ι,
        (∑ j : Fin (2 * k),
          (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) * x j) =
          1 - (∏ s ∈ S, (a i - a s) ^ 2) / h ∧
        (∑ j : Fin (2 * k),
          (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) * x j) ≤ 1 ∧
        ((∑ j : Fin (2 * k),
          (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) * x j) = 1 ↔ i ∈ S) := by
  classical
  let p := squareRoots a S
  let h : ℝ := (∑ i, p.eval (a i)) / (Fintype.card ι : ℝ)
  have hcard : 0 < Fintype.card ι := by omega
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
  have hm0 : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hm
  have hdeg : p.natDegree ≤ 2 * k := by
    dsimp only [p]
    rw [squareRoots_degree]
    omega
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ι, i₀ ∉ S := by
    by_contra hn
    push_neg at hn
    have hsub : (Finset.univ : Finset ι) ⊆ S := by
      intro i _
      exact hn i
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_univ] at hc
    omega
  have hpnon : ∀ i : ι, 0 ≤ p.eval (a i) := fun i => squareRoots_nonneg a S (a i)
  have hpzero : ∀ i : ι, p.eval (a i) = 0 ↔ i ∈ S := fun i => squareRoots_zero_iff a ha S i
  have hpne : p.eval (a i₀) ≠ 0 := fun hz => hi₀ ((hpzero i₀).mp hz)
  have hppos : 0 < p.eval (a i₀) := lt_of_le_of_ne (hpnon i₀) (Ne.symm hpne)
  have hnum : 0 < ∑ i, p.eval (a i) :=
    hppos.trans_le (Finset.single_le_sum (fun i _ => hpnon i) (Finset.mem_univ i₀))
  have hh : 0 < h := div_pos hnum hm
  have hh0 : h ≠ 0 := ne_of_gt hh
  let x : Fin (2 * k) → ℝ := fun j => (-h⁻¹) * p.coeff (j.val + 1)
  have hid : ∀ i : ι,
      (∑ j : Fin (2 * k),
        (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) * x j) =
      1 - p.eval (a i) / h := by
    intro i
    calc
      (∑ j : Fin (2 * k),
        (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) * x j) =
        (-h⁻¹) * ∑ j : Fin (2 * k),
          (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) *
            p.coeff (j.val + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [x]
        ring
      _ = (-h⁻¹) * (p.eval (a i) - h) := by
        rw [centered_eval a p (2 * k) hdeg hm0 i]
      _ = 1 - p.eval (a i) / h := by
        field_simp [hh0]
        <;> ring
  refine ⟨h, hh, ?_, x, ?_⟩
  · dsimp only [h, p]
    simp_rw [eval_squareRoots]
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · simpa only [p, eval_squareRoots] using hid i
    · have hquot : 0 ≤ p.eval (a i) / h := div_nonneg (hpnon i) hh.le
      linarith [hid i]
    · constructor
      · intro heq
        have hquot : p.eval (a i) / h = 0 := by linarith [hid i]
        have hmul := div_mul_cancel₀ (p.eval (a i)) hh0
        rw [hquot, zero_mul] at hmul
        exact (hpzero i).mp hmul.symm
      · intro hi
        rw [hid i, (hpzero i).mpr hi, zero_div, sub_zero]

end Hirsch.MomentSmallFaces



/-! Reused accepted namespace Hirsch.MomentBarycentric; body unchanged. -/

namespace Hirsch.MomentBarycentric

noncomputable def weight {ι : Type*} [DecidableEq ι]
    (a : ι → ℝ) (s : Finset ι) (i : ι) : ℝ :=
  (∏ j ∈ s.erase i, (a i - a j))⁻¹

lemma weight_ne_zero {ι : Type*} [DecidableEq ι]
    (a : ι → ℝ) (ha : Function.Injective a) (s : Finset ι) (i : ι) :
    weight a s i ≠ 0 := by
  unfold weight
  apply inv_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro h
  exact (Finset.mem_erase.mp hj).1 (ha h).symm

/-- The highest coefficient of the interpolant gives exact annihilation.
The weights are constructed, rather than supplied as an affine-dependence premise. -/
lemma weighted_eval_zero {ι : Type*} [DecidableEq ι]
    (a : ι → ℝ) (ha : Function.Injective a) (s : Finset ι)
    (p : Polynomial ℝ) (hp : p.natDegree + 1 < s.card) :
    ∑ i ∈ s, weight a s i * p.eval (a i) = 0 := by
  have hlt : p.natDegree < s.card := by omega
  have hdeg : p.degree < (s.card : WithBot ℕ) :=
    lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast hlt)
  have heq := Lagrange.eq_interpolate (s := s) (v := a) (f := p) ha.injOn hdeg
  have hc := congrArg (fun q : Polynomial ℝ => q.coeff (s.card - 1)) heq
  dsimp only at hc
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff] at hc
  simp only [Polynomial.coeff_C_mul] at hc
  have hb : ∀ i ∈ s,
      (Lagrange.basis s a i).coeff (s.card - 1) = weight a s i := by
    intro i hi
    have h := Lagrange.leadingCoeff_basis (s := s) (v := a) ha.injOn hi
    rw [Polynomial.leadingCoeff, Lagrange.natDegree_basis ha.injOn hi] at h
    exact h
  calc
    (∑ i ∈ s, weight a s i * p.eval (a i)) =
        ∑ i ∈ s, p.eval (a i) * (Lagrange.basis s a i).coeff (s.card - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hb i hi, mul_comm]
    _ = p.coeff (s.card - 1) := hc.symm
    _ = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

lemma sum_zero_both_signs {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hsum : ∑ i ∈ s, f i = 0) (hne : ∃ i ∈ s, f i ≠ 0) :
    (∃ i ∈ s, f i < 0) ∧ (∃ i ∈ s, 0 < f i) := by
  obtain ⟨i, hi, hif⟩ := hne
  constructor
  · by_contra hn
    push_neg at hn
    have hpos : 0 < f i := lt_of_le_of_ne (hn i hi) hif.symm
    have hle := Finset.single_le_sum (fun j hj => hn j hj) hi
    linarith
  · by_contra hn
    push_neg at hn
    have hni : f i < 0 := lt_of_le_of_ne (hn i hi) hif
    have hle := Finset.single_le_sum
      (f := fun j => -f j) (fun j hj => neg_nonneg.mpr (hn j hj)) hi
    have hsumneg : ∑ j ∈ s, -f j = 0 := by
      rw [Finset.sum_neg_distrib, hsum, neg_zero]
    linarith

/-- A nonzero low-degree polynomial nonnegative at the nodes is positive
at some node of EACH barycentric sign. -/
theorem both_signs_positive {ι : Type*} [DecidableEq ι]
    (a : ι → ℝ) (ha : Function.Injective a) (s : Finset ι)
    (p : Polynomial ℝ) (hp : p.natDegree + 1 < s.card) (hp0 : p ≠ 0)
    (hpos : ∀ i ∈ s, 0 ≤ p.eval (a i)) :
    (∃ i ∈ s, weight a s i < 0 ∧ 0 < p.eval (a i)) ∧
    (∃ i ∈ s, 0 < weight a s i ∧ 0 < p.eval (a i)) := by
  have hex : ∃ i ∈ s, 0 < p.eval (a i) := by
    by_contra hn
    push_neg at hn
    have hlt : p.natDegree < s.card := by omega
    have hdeg : p.degree < (s.card : WithBot ℕ) :=
      lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast hlt)
    apply hp0
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero s ha.injOn hdeg
    intro i hi
    exact le_antisymm (hn i hi) (hpos i hi)
  obtain ⟨i, hi, hip⟩ := hex
  have hne : ∃ i ∈ s, weight a s i * p.eval (a i) ≠ 0 :=
    ⟨i, hi, mul_ne_zero (weight_ne_zero a ha s i) (ne_of_gt hip)⟩
  obtain ⟨⟨u, hu, hun⟩, ⟨v, hv, hvp⟩⟩ :=
    sum_zero_both_signs s (fun i => weight a s i * p.eval (a i))
      (weighted_eval_zero a ha s p hp) hne
  constructor
  · refine ⟨u, hu, ?_, ?_⟩
    · by_contra hn
      have hnon := mul_nonneg (le_of_not_gt hn) (hpos u hu)
      linarith
    · have hne : p.eval (a u) ≠ 0 := by
        intro hzero
        simp only [hzero, mul_zero] at hun
        exact (lt_irrefl 0) hun
      exact lt_of_le_of_ne (hpos u hu) hne.symm
  · refine ⟨v, hv, ?_, ?_⟩
    · by_contra hn
      have hnon := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (hpos v hv)
      linarith
    · have hne : p.eval (a v) ≠ 0 := by
        intro hzero
        simp only [hzero, mul_zero] at hvp
        exact (lt_irrefl 0) hvp
      exact lt_of_le_of_ne (hpos v hv) hne.symm

noncomputable def row {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) (i : Fin m) : ℝ :=
  ∑ j : Fin d,
    (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (m : ℝ)) * x j

noncomputable def slack {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) : Polynomial ℝ :=
  1 - ∑ j : Fin d,
    (Polynomial.X ^ (j.val + 1) -
      Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))) * Polynomial.C (x j)

lemma eval_slack {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) (i : Fin m) :
    (slack a x).eval (a i) = 1 - row a x i := by
  simp [slack, row, Polynomial.eval_finsetSum]

lemma degree_slack {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) :
    (slack a x).natDegree ≤ d := by
  unfold slack
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  calc
    ((Polynomial.X ^ (j.val + 1) -
        Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))) *
        Polynomial.C (x j)).natDegree ≤
        (Polynomial.X ^ (j.val + 1) -
          Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))).natDegree +
          (Polynomial.C (x j)).natDegree := Polynomial.natDegree_mul_le
    _ = (Polynomial.X ^ (j.val + 1) -
          Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))).natDegree := by simp
    _ ≤ max (Polynomial.X ^ (j.val + 1) : Polynomial ℝ).natDegree
          (Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ = j.val + 1 := by simp
    _ ≤ d := by omega

lemma sum_row_zero {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hm : (m : ℝ) ≠ 0) : ∑ i, row a x i = 0 := by
  unfold row
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  have hc : (∑ _i : Fin m, (∑ l : Fin m, a l ^ (j.val + 1)) / (m : ℝ)) =
      ∑ l : Fin m, a l ^ (j.val + 1) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hm]
    <;> ring
  rw [hc, sub_self, zero_mul]

lemma slack_ne_zero {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hm : (m : ℝ) ≠ 0) : slack a x ≠ 0 := by
  intro hz
  have hsum : (∑ i : Fin m, (slack a x).eval (a i)) = (m : ℝ) := by
    simp_rw [eval_slack]
    rw [Finset.sum_sub_distrib, sum_row_zero a x hm]
    simp
  have hzero : (∑ i : Fin m, (slack a x).eval (a i)) = 0 := by simp [hz]
  exact hm (hsum.symm.trans hzero)

/-- Constructed moment annihilation and original-H incompatibility on BOTH
sign sides. No optimizer, affine dependence, or rank certificate is assumed. -/
theorem original_nonfaces (d m : ℕ) (a : Fin m → ℝ) (ha : Function.Injective a)
    (s : Finset (Fin m)) (hs : d + 2 ≤ s.card) :
    (∀ i ∈ s, weight a s i ≠ 0) ∧
    (∀ r : ℕ, r ≤ d → ∑ i ∈ s, weight a s i * a i ^ r = 0) ∧
    ∀ x : Fin d → ℝ, (∀ i : Fin m, row a x i ≤ 1) →
      (∃ i ∈ s, weight a s i < 0 ∧ row a x i < 1) ∧
      (∃ i ∈ s, 0 < weight a s i ∧ row a x i < 1) := by
  have hcard := Finset.card_le_card (Finset.subset_univ s)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hmNat : 0 < m := by omega
  have hm : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hmNat)
  refine ⟨fun i _ => weight_ne_zero a ha s i, ?_, ?_⟩
  · intro r hr
    have hp : (Polynomial.X ^ r : Polynomial ℝ).natDegree + 1 < s.card := by
      simp only [Polynomial.natDegree_X_pow]
      omega
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      weighted_eval_zero a ha s (Polynomial.X ^ r) hp
  · intro x hx
    have hp : (slack a x).natDegree + 1 < s.card := by
      have hd := degree_slack a x
      omega
    have hnon : ∀ i ∈ s, 0 ≤ (slack a x).eval (a i) := by
      intro i _
      rw [eval_slack]
      linarith [hx i]
    obtain ⟨⟨u, hu, hw, hpv⟩, ⟨v, hv, hwv, hpw⟩⟩ :=
      both_signs_positive a ha s (slack a x) hp (slack_ne_zero a x hm) hnon
    rw [eval_slack] at hpv hpw
    exact ⟨⟨u, hu, hw, by linarith⟩, ⟨v, hv, hwv, by linarith⟩⟩

end Hirsch.MomentBarycentric




namespace Hirsch.InterleavedMoment

open scoped BigOperators

private lemma prod_erase_pair {I : Type*} [Fintype I] [DecidableEq I]
    (f : I × Bool → ℝ) (i : I) (b : Bool) :
    (∏ z ∈ (Finset.univ : Finset (I × Bool)).erase (i,b), f z) =
      (∏ j ∈ (Finset.univ : Finset I).erase i, f (j,true) * f (j,false)) *
        f (i,!b) := by
  classical
  have hs : (Finset.univ : Finset (I × Bool)).erase (i,b) =
      ((Finset.univ : Finset I).erase i).product Finset.univ ∪ {(i,!b)} := by
    ext z
    rcases z with ⟨j,c⟩
    cases b <;> cases c <;> by_cases h : j = i <;> simp [h]
  have hd : Disjoint (((Finset.univ : Finset I).erase i).product
      (Finset.univ : Finset Bool)) {(i,!b)} := by
    apply Finset.disjoint_left.mpr
    intro z hz ht
    have he : z = (i,!b) := Finset.mem_singleton.mp ht
    subst z
    exact (Finset.mem_erase.mp ((Finset.mem_product.mp hz).1)).1 rfl
  rw [hs, Finset.prod_union hd, Finset.prod_singleton,
    Finset.product_eq_sprod, Finset.prod_product]
  simp_rw [Fintype.prod_bool]

private def node {n : ℕ} (l r : Fin n → ℝ) (p : Fin n × Bool) : ℝ :=
  if p.2 then r p.1 else l p.1

private lemma node_bounds {n : ℕ} (l r : Fin n → ℝ)
    (hpair : ∀ i, l i < r i) (p : Fin n × Bool) :
    l p.1 ≤ node l r p ∧ node l r p ≤ r p.1 := by
  rcases p with ⟨i,b⟩
  cases b <;> simp [node, (hpair i).le]

private lemma node_injective {n : ℕ} (l r : Fin n → ℝ)
    (hpair : ∀ i, l i < r i)
    (hsep : ∀ i j, i < j → r i < l j) : Function.Injective (node l r) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ heq
  have hb := node_bounds l r hpair (i,b)
  have hc := node_bounds l r hpair (j,c)
  have hij : i = j := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hs := hsep i j hlt
      linarith
    · have hs := hsep j i hgt
      linarith
  subst j
  cases b <;> cases c
  · rfl
  · exact False.elim ((ne_of_lt (hpair i)) heq)
  · exact False.elim ((ne_of_gt (hpair i)) heq)
  · rfl

private lemma paired_factor_positive {n : ℕ} (l r : Fin n → ℝ)
    (hpair : ∀ i, l i < r i)
    (hsep : ∀ i j, i < j → r i < l j)
    (i j : Fin n) (b : Bool) (hji : j ≠ i) :
    0 < (node l r (i,b)-r j) * (node l r (i,b)-l j) := by
  have hb := node_bounds l r hpair (i,b)
  rcases lt_or_gt_of_ne hji with hlt | hgt
  · have hs := hsep j i hlt
    exact mul_pos (by linarith) (by linarith [hpair j])
  · have hs := hsep i j hgt
    exact mul_pos_of_neg_of_neg (by linarith [hpair j]) (by linarith)

/-- Pair grouping proves the actual barycentric sign partition. -/
theorem weight_signs {n : ℕ} (l r : Fin n → ℝ)
    (hpair : ∀ i, l i < r i)
    (hsep : ∀ i j, i < j → r i < l j) (i : Fin n) :
    MomentBarycentric.weight (node l r) Finset.univ (i,false) < 0 ∧
    0 < MomentBarycentric.weight (node l r) Finset.univ (i,true) := by
  classical
  have hp : ∀ b : Bool, 0 < ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      (node l r (i,b)-node l r (j,true)) *
        (node l r (i,b)-node l r (j,false)) := by
    intro b
    apply Finset.prod_pos
    intro j hj
    exact paired_factor_positive l r hpair hsep i j b (Finset.mem_erase.mp hj).1
  constructor
  · unfold MomentBarycentric.weight
    have hn : (∏ j ∈ (Finset.univ : Finset (Fin n × Bool)).erase (i,false),
        (node l r (i,false)-node l r j)) < 0 := by
      rw [prod_erase_pair]
      exact mul_neg_of_pos_of_neg (hp false) (by simpa [node] using sub_neg.mpr (hpair i))
    have hh := inv_pos.mpr (neg_pos.mpr hn)
    rw [inv_neg] at hh
    exact neg_pos.mp hh
  · unfold MomentBarycentric.weight
    apply inv_pos.mpr
    rw [prod_erase_pair]
    exact mul_pos (hp true) (by simpa [node] using sub_pos.mpr (hpair i))

/-- Every nonzero degree-2k polynomial nonnegative on the interleaved nodes
is strictly positive at some left node and at some right node. -/
theorem polynomial_positive_both (k : ℕ) (l r : Fin (k+1) → ℝ)
    (hpair : ∀ i, l i < r i)
    (hsep : ∀ i j, i < j → r i < l j)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ 2*k) (hp0 : p ≠ 0)
    (hl : ∀ i, 0 ≤ p.eval (l i)) (hr : ∀ i, 0 ≤ p.eval (r i)) :
    (∃ i, 0 < p.eval (l i)) ∧ (∃ i, 0 < p.eval (r i)) := by
  classical
  have hdeg : p.natDegree+1 <
      (Finset.univ : Finset (Fin (k+1) × Bool)).card := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  have hnon : ∀ z ∈ (Finset.univ : Finset (Fin (k+1) × Bool)),
      0 ≤ p.eval (node l r z) := by
    rintro ⟨i,b⟩ _
    cases b
    · exact hl i
    · exact hr i
  obtain ⟨⟨⟨i,b⟩,_,hw,hv⟩,⟨⟨j,c⟩,_,hw',hv'⟩⟩ :=
    MomentBarycentric.both_signs_positive (node l r)
      (node_injective l r hpair hsep) Finset.univ p hdeg hp0 hnon
  constructor
  · cases b
    · exact ⟨i,hv⟩
    · have hs := (weight_signs l r hpair hsep i).2
      linarith
  · cases c
    · have hs := (weight_signs l r hpair hsep j).1
      linarith
    · exact ⟨j,hv'⟩

end Hirsch.InterleavedMoment

/-- Both interleaved (k+1)-sets are minimal nonfaces of the actual original
mean-centered H system. Strict feasible witnesses are constructed for every
proper subset, not merely asserted by a combinatorial incidence oracle. -/
theorem solution (k m : ℕ) (a : Fin m → ℝ) (ha : Function.Injective a)
    (l r : Fin (k+1) → Fin m)
    (hpair : ∀ i, a (l i) < a (r i))
    (hsep : ∀ i j, i < j → a (r i) < a (l j)) :
    let row : (Fin (2*k) → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin (2*k),
        (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let L : Finset (Fin m) := Finset.univ.image l
    let R : Finset (Fin m) := Finset.univ.image r
    L.card = k+1 ∧ R.card = k+1 ∧ Disjoint L R ∧
    (∀ x : Fin (2*k) → ℝ, (∀ i, row x i ≤ 1) →
      (∃ i ∈ L, row x i < 1) ∧ (∃ i ∈ R, row x i < 1)) ∧
    ∀ S : Finset (Fin m), (S ⊂ L ∨ S ⊂ R) →
      ∃ x : Fin (2*k) → ℝ, ∀ i, row x i ≤ 1 ∧ (row x i = 1 ↔ i ∈ S) := by
  classical
  dsimp only
  let L : Finset (Fin m) := Finset.univ.image l
  let R : Finset (Fin m) := Finset.univ.image r
  let f : Fin (k+1) × Bool → Fin m := fun z => if z.2 then r z.1 else l z.1
  have hf : Function.Injective f := by
    intro u v huv
    apply Hirsch.InterleavedMoment.node_injective (fun i => a (l i))
      (fun i => a (r i)) hpair hsep
    simpa only [f, Hirsch.InterleavedMoment.node, apply_ite] using congrArg a huv
  have hlinj : Function.Injective l := by
    intro i j hij
    have h : f (i,false) = f (j,false) := hij
    exact congrArg Prod.fst (hf h)
  have hrinj : Function.Injective r := by
    intro i j hij
    have h : f (i,true) = f (j,true) := hij
    exact congrArg Prod.fst (hf h)
  have hLc : L.card = k+1 := by
    dsimp [L]
    rw [Finset.card_image_of_injective _ hlinj]
    simp
  have hRc : R.card = k+1 := by
    dsimp [R]
    rw [Finset.card_image_of_injective _ hrinj]
    simp
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro z hzL hzR
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hzL
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hzR
    have heq : f (i,false) = f (j,true) := hi.trans hj.symm
    have hbad : false = true := congrArg Prod.snd (hf heq)
    cases hbad
  refine ⟨hLc,hRc,hdis,?_,?_⟩
  · intro x hx
    have hmNat : 0 < m := by have h := (l 0).isLt; omega
    have hm : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hmNat)
    have hlo : ∀ i, 0 ≤ (Hirsch.MomentBarycentric.slack a x).eval (a (l i)) := by
      intro i
      rw [Hirsch.MomentBarycentric.eval_slack]
      exact sub_nonneg.mpr (hx (l i))
    have hhi : ∀ i, 0 ≤ (Hirsch.MomentBarycentric.slack a x).eval (a (r i)) := by
      intro i
      rw [Hirsch.MomentBarycentric.eval_slack]
      exact sub_nonneg.mpr (hx (r i))
    obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := Hirsch.InterleavedMoment.polynomial_positive_both k
      (fun i => a (l i)) (fun i => a (r i)) hpair hsep
      (Hirsch.MomentBarycentric.slack a x) (Hirsch.MomentBarycentric.degree_slack a x)
      (Hirsch.MomentBarycentric.slack_ne_zero a x hm) hlo hhi
    rw [Hirsch.MomentBarycentric.eval_slack] at hi hj
    exact ⟨⟨l i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,sub_pos.mp hi⟩,
      ⟨r j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,sub_pos.mp hj⟩⟩
  · intro S hs
    have hSk : S.card ≤ k := by
      rcases hs with hs | hs
      · have h : S.card < k+1 := (Finset.card_lt_card hs).trans_eq hLc
        omega
      · have h : S.card < k+1 := (Finset.card_lt_card hs).trans_eq hRc
        omega
    have hkm : k+1 ≤ m := by
      have h := Finset.card_le_card (Finset.subset_univ L)
      simp only [Finset.card_univ,Fintype.card_fin,hLc] at h
      exact h
    have hproper : S.card < Fintype.card (Fin m) := by simp only [Fintype.card_fin]; omega
    obtain ⟨h,hh,hdef,x,hx⟩ := Hirsch.MomentSmallFaces.exact_small_face_witness
      a ha k S hSk hproper
    refine ⟨x,?_⟩
    intro i
    simpa only [Fintype.card_fin] using (hx i).2

#print axioms Hirsch.InterleavedMoment.weight_signs
#print axioms Hirsch.InterleavedMoment.polynomial_positive_both
#print axioms Hirsch.MomentSmallFaces.exact_small_face_witness
#print axioms Hirsch.MomentBarycentric.both_signs_positive
#print axioms solution
