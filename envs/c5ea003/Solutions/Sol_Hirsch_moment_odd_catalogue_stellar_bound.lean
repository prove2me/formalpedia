-- Prove2me | solution 1 for Hirsch.moment_odd_catalogue_stellar_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-17T03:43:21.828684+00:00
-- url     : https://prove2.me/submissions/512da13a-761c-4c0c-b6db-8cab7b7db32c

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
      intro i hi
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

namespace Hirsch.StellarPersistence

/-- Inclusion-minimal nonfaces, with all proper subsets required to be faces. -/
def MinimalNonface (K : Set (Finset ℕ)) (N : Finset ℕ) : Prop :=
  N ∉ K ∧ ∀ T : Finset ℕ, T ⊂ N → T ∈ K

/-- The actual face-membership rule for stellar subdivision at E with fresh z. -/
def Stellar (K : Set (Finset ℕ)) (E : Finset ℕ) (z : ℕ) : Set (Finset ℕ) :=
  {T | if z ∈ T then
      (T.erase z ∪ E) ∈ K ∧ ¬ E ⊆ T.erase z
    else T ∈ K ∧ ¬ E ⊆ T}

/-- Canonical descendant of an old minimal nonface. -/
def Descendant (E : Finset ℕ) (z : ℕ) (N : Finset ℕ) : Finset ℕ :=
  if E ⊆ N then insert z (N \ E) else N

lemma mem_stellar_old {K : Set (Finset ℕ)} {E T : Finset ℕ} {z : ℕ}
    (hz : z ∉ T) :
    T ∈ Stellar K E z ↔ T ∈ K ∧ ¬ E ⊆ T := by
  simp [Stellar, hz]

lemma mem_stellar_new {K : Set (Finset ℕ)} {E T : Finset ℕ} {z : ℕ}
    (hz : z ∈ T) :
    T ∈ Stellar K E z ↔ (T.erase z ∪ E) ∈ K ∧ ¬ E ⊆ T.erase z := by
  simp [Stellar, hz]

lemma erase_descendant {E N : Finset ℕ} {z : ℕ}
    (hEN : E ⊆ N) (hzN : z ∉ N) :
    (insert z (N \ E)).erase z ∪ E = N := by
  ext a
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_sdiff]
  constructor
  · rintro (⟨hneq, ha⟩ | ha)
    · rcases ha with heq | ha
      · exact False.elim (hneq heq)
      · exact ha.1
    · exact hEN ha
  · intro ha
    by_cases haE : a ∈ E
    · exact Or.inr haE
    · refine Or.inl ⟨?_, Or.inr ⟨ha, haE⟩⟩
      intro heq
      subst a
      exact hzN ha

lemma decode_descendant {E N : Finset ℕ} {z : ℕ} (hzN : z ∉ N) :
    (if z ∈ Descendant E z N then
      (Descendant E z N).erase z ∪ E else Descendant E z N) = N := by
  by_cases hEN : E ⊆ N
  · have hzD : z ∈ insert z (N \ E) := Finset.mem_insert_self _ _
    simpa only [Descendant, if_pos hEN, if_pos hzD] using erase_descendant hEN hzN
  · simp [Descendant, hEN, hzN]

lemma descendant_injective {E N M : Finset ℕ} {z : ℕ}
    (hzN : z ∉ N) (hzM : z ∉ M)
    (heq : Descendant E z N = Descendant E z M) : N = M := by
  calc
    N = (if z ∈ Descendant E z N then
        (Descendant E z N).erase z ∪ E else Descendant E z N) :=
      (decode_descendant hzN).symm
    _ = (if z ∈ Descendant E z M then
        (Descendant E z M).erase z ∪ E else Descendant E z M) := by rw [heq]
    _ = M := decode_descendant hzM

lemma edge_not_subset_insert_diff {E N : Finset ℕ} {z : ℕ}
    (hne : E.Nonempty) (hzE : z ∉ E) : ¬ E ⊆ insert z (N \ E) := by
  obtain ⟨a, ha⟩ := hne
  intro h
  rcases Finset.mem_insert.mp (h ha) with heq | hd
  · subst a
    exact hzE ha
  · exact (Finset.mem_sdiff.mp hd).2 ha

/-- Every old minimal nonface has its stated minimal descendant. -/
theorem minimal_descendant {K : Set (Finset ℕ)} {E N : Finset ℕ} {z : ℕ}
    (hne : E.Nonempty) (hzE : z ∉ E) (hzN : z ∉ N)
    (hN : MinimalNonface K N) :
    MinimalNonface (Stellar K E z) (Descendant E z N) := by
  by_cases hEN : E ⊆ N
  · simp only [Descendant, if_pos hEN]
    have hzD : z ∈ insert z (N \ E) := Finset.mem_insert_self _ _
    have hED : ¬ E ⊆ insert z (N \ E) := edge_not_subset_insert_diff hne hzE
    refine ⟨?_, ?_⟩
    · intro h
      have hk := ((mem_stellar_new hzD).mp h).1
      rw [erase_descendant hEN hzN] at hk
      exact hN.1 hk
    · intro T hT
      obtain ⟨hTD, hTne⟩ := Finset.ssubset_iff_subset_ne.mp hT
      have hET : ¬ E ⊆ T := fun h => hED (h.trans hTD)
      by_cases hzT : z ∈ T
      · apply (mem_stellar_new hzT).mpr
        have hUN : T.erase z ∪ E ⊆ N := by
          intro a ha
          rcases Finset.mem_union.mp ha with ht | he
          · have ht' := Finset.mem_erase.mp ht
            rcases Finset.mem_insert.mp (hTD ht'.2) with heq | hd
            · exact False.elim (ht'.1 heq)
            · exact (Finset.mem_sdiff.mp hd).1
          · exact hEN he
        have hUne : T.erase z ∪ E ≠ N := by
          intro heq
          apply hTne
          apply Finset.Subset.antisymm hTD
          intro a ha
          rcases Finset.mem_insert.mp ha with heqz | hd
          · subst a
            exact hzT
          · have had := Finset.mem_sdiff.mp hd
            have hau : a ∈ T.erase z ∪ E := by rw [heq]; exact had.1
            rcases Finset.mem_union.mp hau with ht | he
            · exact (Finset.mem_erase.mp ht).2
            · exact False.elim (had.2 he)
        refine ⟨hN.2 _ (Finset.ssubset_iff_subset_ne.mpr ⟨hUN, hUne⟩), ?_⟩
        intro h
        apply hET
        intro a ha
        exact (Finset.mem_erase.mp (h ha)).2
      · apply (mem_stellar_old hzT).mpr
        have hTN : T ⊆ N := by
          intro a ha
          rcases Finset.mem_insert.mp (hTD ha) with heq | hd
          · subst a
            exact False.elim (hzT ha)
          · exact (Finset.mem_sdiff.mp hd).1
        have hTneN : T ≠ N := by
          intro heq
          apply hET
          simpa only [heq] using hEN
        exact ⟨hN.2 T (Finset.ssubset_iff_subset_ne.mpr ⟨hTN, hTneN⟩), hET⟩
  · simp only [Descendant, if_neg hEN]
    refine ⟨fun h => hN.1 ((mem_stellar_old hzN).mp h).1, ?_⟩
    intro T hT
    have hTN := (Finset.ssubset_iff_subset_ne.mp hT).1
    have hzT : z ∉ T := fun h => hzN (hTN h)
    exact (mem_stellar_old hzT).mpr
      ⟨hN.2 T hT, fun h => hEN (h.trans hTN)⟩

/-- The subdivided face itself is an additional new minimal nonface. -/
theorem born_minimal {K : Set (Finset ℕ)} {E : Finset ℕ} {z : ℕ}
    (hdown : ∀ F ∈ K, ∀ T : Finset ℕ, T ⊆ F → T ∈ K)
    (hE : E ∈ K) (hzE : z ∉ E) :
    MinimalNonface (Stellar K E z) E := by
  refine ⟨?_, ?_⟩
  · intro h
    exact ((mem_stellar_old hzE).mp h).2 (fun _ ha => ha)
  · intro T hT
    obtain ⟨hTE, hTne⟩ := Finset.ssubset_iff_subset_ne.mp hT
    have hzT : z ∉ T := fun h => hzE (hTE h)
    refine (mem_stellar_old hzT).mpr ⟨hdown E hE T hTE, ?_⟩
    intro hET
    exact hTne (Finset.Subset.antisymm hTE hET)

lemma born_not_descendant {K : Set (Finset ℕ)} {E N : Finset ℕ} {z : ℕ}
    (hE : E ∈ K) (hzE : z ∉ E) (hzN : z ∉ N)
    (hN : MinimalNonface K N) : Descendant E z N ≠ E := by
  intro heq
  have hd := decode_descendant (E := E) hzN
  rw [heq] at hd
  have hEq : E = N := by simpa only [if_neg hzE] using hd
  exact hN.1 (hEq ▸ hE)

/-- A finite certified subfamily gains one distinct minimal nonface per step.
Completeness of the supplied old subfamily is not assumed. -/
theorem step_growth
    (V : Finset ℕ) (K : Set (Finset ℕ)) (E : Finset ℕ) (z : ℕ)
    (A : Finset (Finset ℕ))
    (hdown : ∀ F ∈ K, ∀ T : Finset ℕ, T ⊆ F → T ∈ K)
    (hsupport : ∀ F ∈ K, F ⊆ V)
    (hE : E ∈ K) (hsize : 2 ≤ E.card) (hz : z ∉ V)
    (hA : ∀ N ∈ A, N ⊆ V ∧ MinimalNonface K N) :
    ∃ B : Finset (Finset ℕ), B.card = A.card + 1 ∧
      ∀ N ∈ B, N ⊆ insert z V ∧ MinimalNonface (Stellar K E z) N := by
  classical
  have hEV : E ⊆ V := hsupport E hE
  have hzE : z ∉ E := fun h => hz (hEV h)
  have hne : E.Nonempty := Finset.card_pos.mp (by omega)
  have hf : Set.InjOn (Descendant E z) (A : Set (Finset ℕ)) := by
    intro N hN M hM heq
    exact descendant_injective
      (fun h => hz ((hA N hN).1 h))
      (fun h => hz ((hA M hM).1 h)) heq
  have hcard : (A.image (Descendant E z)).card = A.card :=
    Finset.card_image_iff.mpr hf
  have hnot : E ∉ A.image (Descendant E z) := by
    intro h
    obtain ⟨N, hN, heq⟩ := Finset.mem_image.mp h
    exact born_not_descendant hE hzE
      (fun h => hz ((hA N hN).1 h)) (hA N hN).2 heq
  refine ⟨insert E (A.image (Descendant E z)), ?_, ?_⟩
  · simp [hnot, hcard]
  · intro N hN
    rcases Finset.mem_insert.mp hN with heq | himg
    · subst N
      exact ⟨fun a ha => Finset.mem_insert_of_mem (hEV ha), born_minimal hdown hE hzE⟩
    · obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp himg
      have hMV := (hA M hM).1
      refine ⟨?_, minimal_descendant hne hzE (fun h => hz (hMV h)) (hA M hM).2⟩
      intro a ha
      by_cases hEM : E ⊆ M
      · simp only [Descendant, if_pos hEM] at ha
        rcases Finset.mem_insert.mp ha with heq | hd
        · subst a
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hMV (Finset.mem_sdiff.mp hd).1)
      · have haM : a ∈ M := by simpa only [Descendant, if_neg hEM] using ha
        exact Finset.mem_insert_of_mem (hMV haM)

/-- Actual finite stellar sequences preserve every certified root and add one
per subdivision. At flag completion the roots fit into the missing-pair slots. -/
theorem finite_sequence_bound
    (t : ℕ) (V : ℕ → Finset ℕ) (K : ℕ → Set (Finset ℕ))
    (E : ℕ → Finset ℕ) (z : ℕ → ℕ) (A : Finset (Finset ℕ))
    (hdown : ∀ i, i ≤ t → ∀ F ∈ K i, ∀ T : Finset ℕ, T ⊆ F → T ∈ K i)
    (hsupport : ∀ i, i ≤ t → ∀ F ∈ K i, F ⊆ V i)
    (hE : ∀ i, i < t → E i ∈ K i)
    (hsize : ∀ i, i < t → 2 ≤ (E i).card)
    (hz : ∀ i, i < t → z i ∉ V i)
    (hV : ∀ i, i < t → V (i+1) = insert (z i) (V i))
    (hstep : ∀ i, i < t → K (i+1) = Stellar (K i) (E i) (z i))
    (hA : ∀ N ∈ A, N ⊆ V 0 ∧ MinimalNonface (K 0) N)
    (hflag : ∀ N : Finset ℕ, N ⊆ V t → MinimalNonface (K t) N → N.card = 2) :
    A.card + t ≤ ((V 0).card + t).choose 2 := by
  classical
  have grow : ∀ i, i ≤ t → ∃ B : Finset (Finset ℕ),
      B.card = A.card + i ∧ ∀ N ∈ B, N ⊆ V i ∧ MinimalNonface (K i) N := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨A, by simp, hA⟩
    | succ i ih =>
      intro hi
      have hit : i < t := by omega
      have hile : i ≤ t := by omega
      obtain ⟨B, hBcard, hB⟩ := ih hile
      obtain ⟨C, hCcard, hC⟩ := step_growth (V i) (K i) (E i) (z i) B
        (hdown i hile) (hsupport i hile) (hE i hit) (hsize i hit) (hz i hit) hB
      refine ⟨C, by omega, ?_⟩
      intro N hN
      obtain ⟨hNV, hNK⟩ := hC N hN
      constructor
      · simpa only [Nat.succ_eq_add_one, hV i hit] using hNV
      · simpa only [Nat.succ_eq_add_one, hstep i hit] using hNK
  have vcard : ∀ i, i ≤ t → (V i).card = (V 0).card + i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hit : i < t := by omega
      have old := ih (by omega)
      rw [hV i hit]
      simpa [hz i hit, Nat.add_assoc] using congrArg (fun n : ℕ => n+1) old
  obtain ⟨B, hBcard, hB⟩ := grow t (Nat.le_refl t)
  have hsub : B ⊆ Finset.powersetCard 2 (V t) := by
    intro N hN
    exact Finset.mem_powersetCard.mpr ⟨(hB N hN).1, hflag N (hB N hN).1 (hB N hN).2⟩
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_powersetCard, hBcard, vcard t (Nat.le_refl t)] at hcount
  exact hcount

end Hirsch.StellarPersistence

namespace Hirsch.MomentCatalogue

open scoped BigOperators

/-- The original centered moment row, extended to natural-number labels. -/
noncomputable def row (k : ℕ) (x : Fin (2*k) → ℝ) (n : ℕ) : ℝ :=
  ∑ j : Fin (2*k),
    ((n : ℝ) ^ (j.val+1) -
      (∑ i : Fin (4*k+1), (i.val : ℝ) ^ (j.val+1)) / ((4*k+1 : ℕ) : ℝ)) * x j

/-- Actual feasible intersections of original tight rows, not an abstract oracle. -/
def faces (k : ℕ) : Set (Finset ℕ) :=
  {N | N ⊆ Finset.range (4*k+1) ∧ ∃ x : Fin (2*k) → ℝ,
    (∀ i : Fin (4*k+1), row k x i.val ≤ 1) ∧ ∀ n ∈ N, row k x n = 1}

def oddLabel (n : ℕ) : ℕ := 2*n+1

def catalogue (k : ℕ) : Finset (Finset ℕ) :=
  (Finset.powersetCard (k+1) (Finset.range (2*k))).image
    (fun S => S.image oddLabel)

lemma oddLabel_injective : Function.Injective oddLabel := by
  intro i j h
  dsimp only [oddLabel] at h
  omega

lemma image_odd_injective : Function.Injective (fun S : Finset ℕ => S.image oddLabel) := by
  intro S T h
  change S.image oddLabel = T.image oddLabel at h
  apply Finset.Subset.antisymm
  · intro a ha
    have hi : oddLabel a ∈ T.image oddLabel := by
      rw [← h]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hi
    simpa only [oddLabel_injective he] using hb
  · intro a ha
    have hi : oddLabel a ∈ S.image oddLabel := by
      rw [h]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hi
    simpa only [oddLabel_injective he] using hb

/-- Distinct original subsets produce distinct odd-label nonfaces. -/
theorem catalogue_card (k : ℕ) : (catalogue k).card = (2*k).choose (k+1) := by
  unfold catalogue
  rw [Finset.card_image_of_injective _ image_odd_injective,
    Finset.card_powersetCard, Finset.card_range]

lemma small_nat_face (k : ℕ) (T : Finset ℕ)
    (hs : T ⊆ Finset.range (4*k+1)) (hc : T.card ≤ k) : T ∈ faces k := by
  classical
  let a : Fin (4*k+1) → ℝ := fun i => (i.val : ℝ)
  have ha : Function.Injective a := by
    intro i j hij
    apply Fin.ext
    change (i.val : ℝ) = (j.val : ℝ) at hij
    exact_mod_cast hij
  let U : Finset (Fin (4*k+1)) := Finset.univ.filter (fun i => i.val ∈ T)
  have hu : U.image Fin.val = T := by
    ext n
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hi).2
    · intro hn
      have hb : n < 4*k+1 := Finset.mem_range.mp (hs hn)
      exact Finset.mem_image.mpr
        ⟨⟨n,hb⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩, rfl⟩
  have huc : U.card = T.card := by
    rw [← hu, Finset.card_image_of_injective _ Fin.val_injective]
  have huk : U.card ≤ k := by omega
  have hup : U.card < Fintype.card (Fin (4*k+1)) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨h, hh, he, x, hx⟩ :=
    Hirsch.MomentSmallFaces.exact_small_face_witness a ha k U huk hup
  refine ⟨hs,x,?_,?_⟩
  · intro i
    simpa only [row,a,Fintype.card_fin] using (hx i).2.1
  · intro n hn
    let i : Fin (4*k+1) := ⟨n,Finset.mem_range.mp (hs hn)⟩
    have hi : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
    simpa only [row,a,i,Fintype.card_fin] using (hx i).2.2.mpr hi

/-- Every selected odd subset is incompatible; the even partners are constructed. -/
lemma odd_subset_not_face (k : ℕ) (S : Finset ℕ)
    (hs : S ⊆ Finset.range (2*k)) (hc : S.card = k+1) :
    S.image oddLabel ∉ faces k := by
  classical
  let e : Fin (k+1) ↪o ℕ := S.orderEmbOfFin hc
  have hem : ∀ i : Fin (k+1), e i ∈ S := fun i => S.orderEmbOfFin_mem hc i
  have heb : ∀ i : Fin (k+1), e i < 2*k :=
    fun i => Finset.mem_range.mp (hs (hem i))
  let l : Fin (k+1) → Fin (4*k+1) :=
    fun i => ⟨2*e i+1, by have h := heb i; omega⟩
  let r : Fin (k+1) → Fin (4*k+1) :=
    fun i => ⟨2*e i+2, by have h := heb i; omega⟩
  let a : Fin (4*k+1) → ℝ := fun i => (i.val : ℝ)
  have hp : ∀ i, a (l i) < a (r i) := by
    intro i
    change ((2*e i+1 : ℕ) : ℝ) < ((2*e i+2 : ℕ) : ℝ)
    exact_mod_cast (show 2*e i+1 < 2*e i+2 by omega)
  have hsep : ∀ i j, i < j → a (r i) < a (l j) := by
    intro i j hij
    have hh : e i < e j := e.strictMono hij
    change ((2*e i+2 : ℕ) : ℝ) < ((2*e j+1 : ℕ) : ℝ)
    exact_mod_cast (show 2*e i+2 < 2*e j+1 by omega)
  rintro ⟨_,x,hx,ht⟩
  have hm : ((4*k+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hl : ∀ i, 0 ≤ (Hirsch.MomentBarycentric.slack a x).eval (a (l i)) := by
    intro i
    rw [Hirsch.MomentBarycentric.eval_slack]
    exact sub_nonneg.mpr (hx (l i))
  have hr : ∀ i, 0 ≤ (Hirsch.MomentBarycentric.slack a x).eval (a (r i)) := by
    intro i
    rw [Hirsch.MomentBarycentric.eval_slack]
    exact sub_nonneg.mpr (hx (r i))
  obtain ⟨⟨i,hi⟩,_⟩ := Hirsch.InterleavedMoment.polynomial_positive_both k
    (fun j => a (l j)) (fun j => a (r j)) hp hsep
    (Hirsch.MomentBarycentric.slack a x) (Hirsch.MomentBarycentric.degree_slack a x)
    (Hirsch.MomentBarycentric.slack_ne_zero a x hm) hl hr
  rw [Hirsch.MomentBarycentric.eval_slack] at hi
  have hit : row k x (oddLabel (e i)) = 1 :=
    ht _ (Finset.mem_image.mpr ⟨e i,hem i,rfl⟩)
  change 0 < 1 - row k x (oddLabel (e i)) at hi
  rw [hit, sub_self] at hi
  exact (lt_irrefl (0 : ℝ)) hi

/-- Complete geometric catalogue, with no separator or nonface premise. -/
theorem catalogue_minimal (k : ℕ) (N : Finset ℕ) (hN : N ∈ catalogue k) :
    N ⊆ Finset.range (4*k+1) ∧ Hirsch.StellarPersistence.MinimalNonface (faces k) N := by
  classical
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hN
  obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hS
  have hsub : S.image oddLabel ⊆ Finset.range (4*k+1) := by
    intro n hn
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
    have hb := Finset.mem_range.mp (hs hi)
    apply Finset.mem_range.mpr
    dsimp only [oddLabel]
    omega
  have hcard : (S.image oddLabel).card = k+1 := by
    rw [Finset.card_image_of_injective _ oddLabel_injective,hc]
  refine ⟨hsub,odd_subset_not_face k S hs hc,?_⟩
  intro T hT
  have htc := Finset.card_lt_card hT
  have hts : T ⊆ Finset.range (4*k+1) :=
    (Finset.ssubset_iff_subset_ne.mp hT).1.trans hsub
  exact small_nat_face k T hts (by omega)

/-- The actual initial moment-row face family supplies the large finite A. -/
theorem stellar_bound (k t : ℕ)
    (V : ℕ → Finset ℕ) (K : ℕ → Set (Finset ℕ))
    (E : ℕ → Finset ℕ) (z : ℕ → ℕ)
    (hV0 : V 0 = Finset.range (4*k+1)) (hK0 : K 0 = faces k)
    (hdown : ∀ i, i ≤ t → ∀ F ∈ K i, ∀ T : Finset ℕ, T ⊆ F → T ∈ K i)
    (hsupport : ∀ i, i ≤ t → ∀ F ∈ K i, F ⊆ V i)
    (hE : ∀ i, i < t → E i ∈ K i)
    (hsize : ∀ i, i < t → 2 ≤ (E i).card)
    (hz : ∀ i, i < t → z i ∉ V i)
    (hV : ∀ i, i < t → V (i+1) = insert (z i) (V i))
    (hstep : ∀ i, i < t → K (i+1) = Hirsch.StellarPersistence.Stellar (K i) (E i) (z i))
    (hflag : ∀ N : Finset ℕ, N ⊆ V t →
      Hirsch.StellarPersistence.MinimalNonface (K t) N → N.card = 2) :
    (2*k).choose (k+1) + t ≤ (4*k+1+t).choose 2 := by
  have hA : ∀ N ∈ catalogue k,
      N ⊆ V 0 ∧ Hirsch.StellarPersistence.MinimalNonface (K 0) N := by
    intro N hn
    simpa only [hV0,hK0] using catalogue_minimal k N hn
  have h := Hirsch.StellarPersistence.finite_sequence_bound
    t V K E z (catalogue k) hdown hsupport hE hsize hz hV hstep hA hflag
  rw [catalogue_card,hV0,Finset.card_range] at h
  exact h

end Hirsch.MomentCatalogue

/-- A concrete moment-row catalogue forces this size bound on every actual
finite forward stellar flag completion; no catalogue size is assumed. -/
theorem solution (k t : ℕ)
    (V : ℕ → Finset ℕ) (K : ℕ → Set (Finset ℕ))
    (E : ℕ → Finset ℕ) (z : ℕ → ℕ)
    (hV0 : V 0 = Finset.range (4*k+1))
    (hK0 : K 0 = {N | N ⊆ Finset.range (4*k+1) ∧ ∃ x : Fin (2*k) → ℝ,
      (∀ i : Fin (4*k+1),
        (∑ j : Fin (2*k), ((i.val : ℝ) ^ (j.val+1) -
          (∑ l : Fin (4*k+1), (l.val : ℝ) ^ (j.val+1)) / ((4*k+1 : ℕ) : ℝ)) * x j) ≤ 1) ∧
      ∀ n ∈ N,
        (∑ j : Fin (2*k), ((n : ℝ) ^ (j.val+1) -
          (∑ l : Fin (4*k+1), (l.val : ℝ) ^ (j.val+1)) / ((4*k+1 : ℕ) : ℝ)) * x j) = 1})
    (hdown : ∀ i, i ≤ t → ∀ F ∈ K i, ∀ T : Finset ℕ, T ⊆ F → T ∈ K i)
    (hsupport : ∀ i, i ≤ t → ∀ F ∈ K i, F ⊆ V i)
    (hE : ∀ i, i < t → E i ∈ K i)
    (hsize : ∀ i, i < t → 2 ≤ (E i).card)
    (hz : ∀ i, i < t → z i ∉ V i)
    (hV : ∀ i, i < t → V (i+1) = insert (z i) (V i))
    (hstep : ∀ i, i < t → K (i+1) =
      {T | if z i ∈ T then
        (T.erase (z i) ∪ E i) ∈ K i ∧ ¬ E i ⊆ T.erase (z i)
        else T ∈ K i ∧ ¬ E i ⊆ T})
    (hflag : ∀ N : Finset ℕ, N ⊆ V t →
      (N ∉ K t ∧ ∀ T : Finset ℕ, T ⊂ N → T ∈ K t) → N.card = 2) :
    (2*k).choose (k+1) + t ≤ (4*k+1+t).choose 2 := by
  exact Hirsch.MomentCatalogue.stellar_bound k t V K E z
    hV0 hK0 hdown hsupport hE hsize hz hV hstep hflag

#print axioms Hirsch.MomentCatalogue.catalogue_card
#print axioms Hirsch.MomentCatalogue.odd_subset_not_face
#print axioms Hirsch.MomentCatalogue.catalogue_minimal
#print axioms Hirsch.MomentCatalogue.stellar_bound
#print axioms solution
