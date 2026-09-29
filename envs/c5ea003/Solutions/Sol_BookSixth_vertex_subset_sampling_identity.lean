-- Prove2me | solution 1 for BookSixth.vertex_subset_sampling_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T12:21:17.203924+00:00
-- url     : https://prove2.me/submissions/c9079d26-6274-43dc-8b22-8fa64853f651

import Mathlib
open scoped BigOperators

theorem solution {N : ℕ} (T : Finset (Fin N)) (p : ℝ) :
    (∑ x : Fin N → Bool,
      if ∀ v ∈ T, x v = true then
        ∏ v : Fin N, if x v then p else 1-p
      else 0) = p^T.card := by
  classical
  let w : Bool → ℝ := fun b => if b then p else 1-p
  let f : Fin N → Bool → ℝ := fun v b =>
    if v ∈ T then (if b then p else 0) else w b
  have hpoint (x : Fin N → Bool) :
      (if ∀ v ∈ T, x v = true then ∏ v, w (x v) else 0) =
        ∏ v, f v (x v) := by
    have hf : (∏ v, f v (x v)) =
        ∏ v, if v ∈ T → x v = true then w (x v) else 0 := by
      apply Finset.prod_congr rfl
      intro v hv
      by_cases ht : v ∈ T <;> cases hx : x v <;> simp [f, w, ht, hx]
    rw [hf, Fintype.prod_ite_zero]
    by_cases hx : ∀ v ∈ T, x v = true
    · simp only [if_pos hx]
    · simp only [if_neg hx]
  change (∑ x : Fin N → Bool,
    if ∀ v ∈ T, x v = true then ∏ v, w (x v) else 0) = _
  calc
    _ = ∑ x : Fin N → Bool, ∏ v, f v (x v) :=
      Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = ∏ v : Fin N, ∑ b : Bool, f v b := (Fintype.prod_sum f).symm
    _ = ∏ v : Fin N, if v ∈ T then p else 1 := by
      apply Finset.prod_congr rfl
      intro v hv
      by_cases ht : v ∈ T <;> simp [f, w, ht, Fintype.sum_bool]
    _ = p^T.card := by simp [Fintype.prod_ite_mem]
