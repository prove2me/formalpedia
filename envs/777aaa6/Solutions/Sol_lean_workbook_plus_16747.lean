-- Prove2me | solution 1 for lean_workbook_plus_16747
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:33.089607+00:00
-- url     : https://prove2.me/submissions/ae979ca2-e586-4d8c-a677-0fd706911a0d

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

private theorem balanced_signs {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (hs : ∑ i, a i = 0) : (∃ i, 0 < a i) ↔ ∃ i, a i < 0 := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero
      (fun j => -a j) (by simp only [Finset.sum_neg_distrib, hs, neg_zero])
      ⟨i, Finset.mem_univ i, by linarith⟩
    exact ⟨j, by linarith⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero a hs
      ⟨i, Finset.mem_univ i, ne_of_lt hi⟩
    exact ⟨j, hj⟩

private theorem nonempty_equal_unions (n : ℕ) (X : Fin (n + 1) → Set (Fin n))
    (hX : ∀ i, X i ≠ ∅) :
    ∃ I J : Finset (Fin (n + 1)), I.Nonempty ∧ J.Nonempty ∧
      I ∩ J = ∅ ∧ (⋃ i ∈ I, X i) = ⋃ j ∈ J, X j := by
  classical
  let v : Fin (n + 1) → Fin n → ℝ := fun i x => if x ∈ X i then 1 else 0
  have hdep : ¬ LinearIndependent ℝ v := by
    intro h
    have hcard := h.fintype_card_le_finrank
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcard
    omega
  obtain ⟨c, hc, i, hci⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hbalance (x : Fin n) :
      (∃ j, 0 < c j ∧ x ∈ X j) ↔ ∃ j, c j < 0 ∧ x ∈ X j := by
    have hcoord : ∑ j, (if x ∈ X j then c j else 0) = 0 := by
      simpa [v, Finset.sum_apply] using congr_fun hc x
    have hb := balanced_signs (fun j => if x ∈ X j then c j else 0) hcoord
    have hp (j) : (0 < if x ∈ X j then c j else 0) ↔ 0 < c j ∧ x ∈ X j := by
      by_cases hx : x ∈ X j <;> simp [hx]
    have hn (j) : (if x ∈ X j then c j else 0) < 0 ↔ c j < 0 ∧ x ∈ X j := by
      by_cases hx : x ∈ X j <;> simp [hx]
    simpa only [hp, hn] using hb
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr (hX i)
  have hpos : ∃ j, 0 < c j ∧ x ∈ X j := by
    rcases lt_or_gt_of_ne hci with hi | hi
    · exact (hbalance x).mpr ⟨i, hi, hx⟩
    · exact ⟨i, hi, hx⟩
  obtain ⟨j, hj, hxj⟩ := hpos
  obtain ⟨k, hk, _⟩ := (hbalance x).mp ⟨j, hj, hxj⟩
  let I := Finset.univ.filter (fun j => 0 < c j)
  let J := Finset.univ.filter (fun j => c j < 0)
  refine ⟨I, J, ⟨j, by simp [I, hj]⟩, ⟨k, by simp [J, hk]⟩, ?_, ?_⟩
  · ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, I, J]
    rintro ⟨hj, hk⟩
    linarith
  · ext x
    simpa only [Set.mem_iUnion, exists_prop, Finset.mem_filter, Finset.mem_univ, true_and,
      I, J] using hbalance x

theorem solution (n : ℕ) (X : Fin (n + 1) → Set (Fin n)) (hX : ∀ i, X i ≠ ∅) :
    ∃ I J : Finset (Fin (n + 1)), (I ∩ J = ∅ ∧ ⋃ i ∈ I, X i = ⋃ j ∈ J, X j) := by
  obtain ⟨I, J, _, _, hdisj, heq⟩ := nonempty_equal_unions n X hX
  exact ⟨I, J, hdisj, heq⟩
