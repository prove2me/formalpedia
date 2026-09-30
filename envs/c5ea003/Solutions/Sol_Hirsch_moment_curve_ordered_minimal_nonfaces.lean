-- Prove2me | solution 1 for Hirsch.moment_curve_ordered_minimal_nonfaces
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-17T03:08:14.714956+00:00
-- url     : https://prove2.me/submissions/83b6f1bb-cd20-431f-92ff-6f1eb201a917

import Mathlib

open scoped BigOperators

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

namespace Hirsch.OrderedMoment

open Hirsch.MomentBarycentric

/-- Separate lower and upper ordered factors; no sign premise is supplied. -/
lemma denominator_split {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (c i - c j)) =
      (∏ j ∈ Finset.Iio i, (c i - c j)) *
        ((-1 : ℝ) ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, (c j - c i)) := by
  classical
  have hs : (Finset.univ : Finset (Fin n)).erase i =
      Finset.Iio i ∪ Finset.Ioi i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi]
    constructor
    · intro hn
      rcases lt_trichotomy j i with h | h | h
      · exact Or.inl h
      · exact False.elim (hn h)
      · exact Or.inr h
    · rintro (h | h)
      · exact ne_of_lt h
      · exact ne_of_gt h
  have hd : Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact lt_asymm (Finset.mem_Iio.mp hj) (Finset.mem_Ioi.mp hk)
  have hu : (∏ j ∈ Finset.Ioi i, (c i - c j)) =
      (-1 : ℝ) ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, (c j - c i) := by
    calc
      (∏ j ∈ Finset.Ioi i, (c i - c j)) =
          ∏ j ∈ Finset.Ioi i, (-1 : ℝ) * (c j - c i) := by
        apply Finset.prod_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [hs, Finset.prod_union hd, hu]

lemma ordered_products_pos {n : ℕ} (c : Fin n → ℝ) (hc : StrictMono c) (i : Fin n) :
    0 < (∏ j ∈ Finset.Iio i, (c i - c j)) ∧
    0 < (∏ j ∈ Finset.Ioi i, (c j - c i)) := by
  constructor
  · apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hc (Finset.mem_Iio.mp hj))
  · apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hc (Finset.mem_Ioi.mp hj))

lemma weight_even_pos (k : ℕ) (c : Fin (2 * k + 3) → ℝ)
    (hc : StrictMono c) (i : Fin (2 * k + 3)) (hi : i.val % 2 = 0) :
    0 < weight c Finset.univ i := by
  have hcnt : (Finset.Ioi i).card = 2 * (k + 1 - i.val / 2) := by
    rw [Fin.card_Ioi]
    have hib := i.isLt
    omega
  have hsign : (-1 : ℝ) ^ (Finset.Ioi i).card = 1 := by
    rw [hcnt, pow_mul]
    norm_num
  obtain ⟨hl, hu⟩ := ordered_products_pos c hc i
  have hp : 0 < ∏ j ∈ (Finset.univ : Finset (Fin (2 * k + 3))).erase i,
      (c i - c j) := by
    rw [denominator_split c i, hsign, one_mul]
    exact mul_pos hl hu
  simpa only [weight, one_div] using div_pos (show (0 : ℝ) < 1 by norm_num) hp

lemma weight_odd_neg (k : ℕ) (c : Fin (2 * k + 3) → ℝ)
    (hc : StrictMono c) (i : Fin (2 * k + 3)) (hi : i.val % 2 = 1) :
    weight c Finset.univ i < 0 := by
  have hcnt : (Finset.Ioi i).card = 2 * (k - i.val / 2) + 1 := by
    rw [Fin.card_Ioi]
    have hib := i.isLt
    omega
  have hsign : (-1 : ℝ) ^ (Finset.Ioi i).card = -1 := by
    rw [hcnt, pow_add, pow_mul]
    norm_num
  obtain ⟨hl, hu⟩ := ordered_products_pos c hc i
  have hp : (∏ j ∈ (Finset.univ : Finset (Fin (2 * k + 3))).erase i,
      (c i - c j)) < 0 := by
    rw [denominator_split c i, hsign, neg_one_mul]
    exact mul_neg_of_pos_of_neg hl (neg_lt_zero.mpr hu)
  simpa only [weight, one_div] using
    div_neg_of_pos_of_neg (show (0 : ℝ) < 1 by norm_num) hp

/-- The sign partition is derived from strict order, not assumed as an oracle. -/
theorem negative_weight_iff_odd (k : ℕ) (c : Fin (2 * k + 3) → ℝ)
    (hc : StrictMono c) (i : Fin (2 * k + 3)) :
    weight c Finset.univ i < 0 ↔ i.val % 2 = 1 := by
  constructor
  · intro hn
    by_contra hnot
    have heven : i.val % 2 = 0 := by omega
    have hp := weight_even_pos k c hc i heven
    linarith
  · exact weight_odd_neg k c hc i

def oddIndex (k : ℕ) (j : Fin (k + 1)) : Fin (2 * k + 3) :=
  ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩

lemma oddIndex_injective (k : ℕ) : Function.Injective (oddIndex k) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  dsimp only [oddIndex] at hv
  omega

lemma oddIndex_exists (k : ℕ) (i : Fin (2 * k + 3)) (hi : i.val % 2 = 1) :
    ∃ j : Fin (k + 1), oddIndex k j = i := by
  have hib := i.isLt
  refine ⟨⟨i.val / 2, by omega⟩, ?_⟩
  apply Fin.ext
  dsimp only [oddIndex]
  omega

def oddLabels {k m : ℕ} (b : Fin (2 * k + 3) → Fin m) : Finset (Fin m) :=
  Finset.univ.image (fun j : Fin (k + 1) => b (oddIndex k j))

lemma card_oddLabels {k m : ℕ} (b : Fin (2 * k + 3) → Fin m)
    (hb : Function.Injective b) : (oddLabels b).card = k + 1 := by
  have hf : Function.Injective (fun j : Fin (k + 1) => b (oddIndex k j)) :=
    hb.comp (oddIndex_injective k)
  have hc : (Finset.univ.image (fun j : Fin (k + 1) => b (oddIndex k j))).card =
      (Finset.univ : Finset (Fin (k + 1))).card := Finset.card_image_iff.mpr hf.injOn
  simpa only [oddLabels, Finset.card_univ, Fintype.card_fin] using hc

/-- At every feasible point, some selected odd-rank ORIGINAL inequality is strict.
The slack polynomial retains the average over all m original labels. -/
theorem odd_row_strict (k m : ℕ) (a : Fin m → ℝ)
    (b : Fin (2 * k + 3) → Fin m) (hab : StrictMono (fun j => a (b j)))
    (x : Fin (2 * k) → ℝ) (hx : ∀ i : Fin m, row a x i ≤ 1) :
    ∃ i ∈ oddLabels b, row a x i < 1 := by
  have hmNat : 0 < m := by
    have hb := (b ⟨0, by omega⟩).isLt
    omega
  have hm : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hmNat)
  have hp : (slack a x).natDegree + 1 <
      (Finset.univ : Finset (Fin (2 * k + 3))).card := by
    have hh := degree_slack a x
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hnon : ∀ j ∈ (Finset.univ : Finset (Fin (2 * k + 3))),
      0 ≤ (slack a x).eval (a (b j)) := by
    intro j _
    rw [eval_slack]
    linarith [hx (b j)]
  obtain ⟨⟨i, _, hw, hs⟩, _⟩ := both_signs_positive
    (fun j => a (b j)) hab.injective Finset.univ (slack a x)
    hp (slack_ne_zero a x hm) hnon
  have hi : i.val % 2 = 1 := (negative_weight_iff_odd k _ hab i).mp hw
  obtain ⟨j, hj⟩ := oddIndex_exists k i hi
  refine ⟨b i, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg b hj⟩
  · rw [eval_slack] at hs
    linarith

/-- Full minimal incompatibility, not only a conditional sign-side exclusion. -/
theorem ordered_minimal_nonface (k m : ℕ) (a : Fin m → ℝ)
    (ha : Function.Injective a) (b : Fin (2 * k + 3) → Fin m)
    (hab : StrictMono (fun j => a (b j))) :
    (oddLabels b).card = k + 1 ∧
    (¬ ∃ x : Fin (2 * k) → ℝ,
      (∀ i : Fin m, row a x i ≤ 1) ∧ ∀ i ∈ oddLabels b, row a x i = 1) ∧
    ∀ T : Finset (Fin m), T ⊂ oddLabels b →
      ∃ x : Fin (2 * k) → ℝ,
        (∀ i : Fin m, row a x i ≤ 1) ∧
        ∀ i : Fin m, row a x i = 1 ↔ i ∈ T := by
  have hb : Function.Injective b := by
    intro i j h
    exact hab.injective (congrArg a h)
  have hcard := card_oddLabels b hb
  refine ⟨hcard, ?_, ?_⟩
  · rintro ⟨x, hx, ht⟩
    obtain ⟨i, hi, hstrict⟩ := odd_row_strict k m a b hab x hx
    rw [ht i hi] at hstrict
    exact (lt_irrefl (1 : ℝ)) hstrict
  · intro T hT
    have hlt := Finset.card_lt_card hT
    have hsize : T.card ≤ k := by omega
    have hNle := Finset.card_le_card (Finset.subset_univ (oddLabels b))
    have hproper : T.card < Fintype.card (Fin m) := by
      simp only [Finset.card_univ] at hNle
      omega
    obtain ⟨h, hh, he, x, hx⟩ :=
      Hirsch.MomentSmallFaces.exact_small_face_witness a ha k T hsize hproper
    refine ⟨x, ?_, ?_⟩
    · intro i
      simpa only [row, Fintype.card_fin] using (hx i).2.1
    · intro i
      simpa only [row, Fintype.card_fin] using (hx i).2.2

end Hirsch.OrderedMoment

/-- Alternating labels of any strictly ordered embedded moment chain form an
explicit minimal incompatible original-facet family, with exact proper faces. -/
theorem solution (k m : ℕ) (a : Fin m → ℝ) (ha : Function.Injective a)
    (b : Fin (2 * k + 3) → Fin m) (hab : StrictMono (fun j => a (b j))) :
    let N : Finset (Fin m) := Finset.univ.image
      (fun j : Fin (k + 1) => b ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩)
    let row : (Fin (2 * k) → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin (2 * k),
        (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (m : ℝ)) * x j
    N.card = k + 1 ∧
    (¬ ∃ x : Fin (2 * k) → ℝ,
      (∀ i : Fin m, row x i ≤ 1) ∧ ∀ i ∈ N, row x i = 1) ∧
    ∀ T : Finset (Fin m), T ⊂ N →
      ∃ x : Fin (2 * k) → ℝ,
        (∀ i : Fin m, row x i ≤ 1) ∧
        ∀ i : Fin m, row x i = 1 ↔ i ∈ T := by
  exact Hirsch.OrderedMoment.ordered_minimal_nonface k m a ha b hab

#print axioms Hirsch.OrderedMoment.negative_weight_iff_odd
#print axioms Hirsch.OrderedMoment.card_oddLabels
#print axioms Hirsch.OrderedMoment.odd_row_strict
#print axioms Hirsch.OrderedMoment.ordered_minimal_nonface
#print axioms solution
