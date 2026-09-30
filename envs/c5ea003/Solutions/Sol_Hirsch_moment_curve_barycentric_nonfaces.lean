-- Prove2me | solution 1 for Hirsch.moment_curve_barycentric_nonfaces
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-17T02:19:04.199294+00:00
-- url     : https://prove2.me/submissions/7fe04fd6-07d9-4ffc-83d0-bc44f67374a6

import Mathlib

open scoped BigOperators

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

/-- Exact barycentric sign obstructions for the original mean-centered moment inequalities. -/
theorem solution (d m : ℕ) (a : Fin m → ℝ) (ha : Function.Injective a)
    (s : Finset (Fin m)) (hs : d + 2 ≤ s.card) :
    let w : Fin m → ℝ := fun i => (∏ j ∈ s.erase i, (a i - a j))⁻¹
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d,
        (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (m : ℝ)) * x j
    (∀ i ∈ s, w i ≠ 0) ∧
    (∀ r : ℕ, r ≤ d → ∑ i ∈ s, w i * a i ^ r = 0) ∧
    ∀ x : Fin d → ℝ, (∀ i : Fin m, row x i ≤ 1) →
      (∃ i ∈ s, w i < 0 ∧ row x i < 1) ∧
      (∃ i ∈ s, 0 < w i ∧ row x i < 1) := by
  exact Hirsch.MomentBarycentric.original_nonfaces d m a ha s hs

#print axioms Hirsch.MomentBarycentric.weighted_eval_zero
#print axioms Hirsch.MomentBarycentric.both_signs_positive
#print axioms Hirsch.MomentBarycentric.slack_ne_zero
#print axioms Hirsch.MomentBarycentric.original_nonfaces
#print axioms solution
