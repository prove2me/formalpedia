-- Prove2me | solution 1 for Hirsch.moment_curve_exact_small_face_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-17T00:36:01.450765+00:00
-- url     : https://prove2.me/submissions/bd1595ff-d987-4a5b-8f0c-017dec561971

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

/-- The complete public statement uses only Mathlib types and the explicit
mean-centered moment inequalities; no support witness is assumed. -/
theorem solution {ι : Type*} [Fintype ι]
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
  exact Hirsch.MomentSmallFaces.exact_small_face_witness a ha k S hS hproper

#print axioms Hirsch.MomentSmallFaces.squareRoots_degree
#print axioms Hirsch.MomentSmallFaces.average_split
#print axioms Hirsch.MomentSmallFaces.centered_eval
#print axioms Hirsch.MomentSmallFaces.exact_small_face_witness
#print axioms solution
