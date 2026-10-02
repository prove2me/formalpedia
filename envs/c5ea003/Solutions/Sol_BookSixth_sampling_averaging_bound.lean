-- Prove2me | solution 1 for BookSixth.sampling_averaging_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T12:48:36.032459+00:00
-- url     : https://prove2.me/submissions/5582fd3c-ee27-43a4-9d8c-38e81ede22bb

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_vertex_subset_sampling_identity
open scoped BigOperators
open BookSixth

private theorem weighted_count {N : ℕ} {α : Type*} (s : Finset α)
    (T : α → Finset (Fin N)) (k : ℕ) (hk : ∀ a ∈ s, (T a).card = k)
    (p : ℝ) :
    (∑ x : Fin N → Bool, (∏ v : Fin N, if x v then p else 1-p) *
      (∑ a ∈ s, if ∀ v ∈ T a, x v = true then (1 : ℝ) else 0)) =
      (s.card : ℝ) * p^k := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a ∈ s, p^k := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _ = ∑ x : Fin N → Bool,
            if ∀ v ∈ T a, x v = true then
              ∏ v : Fin N, if x v then p else 1-p else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          split_ifs <;> simp
        _ = p^(T a).card := BookSixth.vertex_subset_sampling_identity (T a) p
        _ = p^k := by rw [hk a ha]
    _ = (s.card : ℝ) * p^k := by simp

-- The geometric premise is deliberately separate from the averaging argument.
theorem solution {N M : ℕ} (D : PlaneDrawing N M)
    (hgeom : ∀ x : Fin N → Bool,
      (∑ e : Fin M, if x (D.left e) = true ∧ x (D.right e) = true
        then (1 : ℝ) else 0) ≤
      3 * (∑ v : Fin N, if x v = true then (1 : ℝ) else 0) +
      ∑ c ∈ D.crossings,
        if x (D.left c.1.1) = true ∧ x (D.right c.1.1) = true ∧
          x (D.left c.1.2) = true ∧ x (D.right c.1.2) = true
        then (1 : ℝ) else 0)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p^2 * (M : ℝ) ≤ 3*p*(N : ℝ) + p^4*(D.crossings.card : ℝ) := by
  classical
  let w : (Fin N → Bool) → ℝ := fun x =>
    ∏ v : Fin N, if x v then p else 1-p
  have hw (x : Fin N → Bool) : 0 ≤ w x := by
    apply Finset.prod_nonneg
    intro v hv
    cases x v <;> simp [hp, sub_nonneg.mpr hp1]
  have hv : (∑ x : Fin N → Bool, w x *
      (∑ v : Fin N, if x v = true then (1 : ℝ) else 0)) = (N : ℝ)*p := by
    simpa [w] using weighted_count (Finset.univ : Finset (Fin N))
      (fun v => {v}) 1 (by intros; simp) p
  have he : (∑ x : Fin N → Bool, w x *
      (∑ e : Fin M, if x (D.left e) = true ∧ x (D.right e) = true
        then (1 : ℝ) else 0)) = (M : ℝ)*p^2 := by
    simpa [w] using weighted_count (Finset.univ : Finset (Fin M))
      (fun e => {D.left e, D.right e}) 2
      (by intro e he; exact Finset.card_pair (D.no_loop e)) p
  have hc : (∑ x : Fin N → Bool, w x *
      (∑ c ∈ D.crossings,
        if x (D.left c.1.1) = true ∧ x (D.right c.1.1) = true ∧
          x (D.left c.1.2) = true ∧ x (D.right c.1.2) = true
        then (1 : ℝ) else 0)) = (D.crossings.card : ℝ)*p^4 := by
    have hcard (c) (hc : c ∈ D.crossings) :
        ({D.left c.1.1, D.right c.1.1, D.left c.1.2, D.right c.1.2} :
          Finset (Fin N)).card = 4 := by
      obtain ⟨hll, hlr, hrl, hrr⟩ := D.independent_crossings c.1.1 c.1.2 c.2 hc
      simp [Finset.card_insert_of_notMem, D.no_loop, hll, hlr, hrl, hrr]
    simpa [w, and_assoc] using weighted_count D.crossings
      (fun c => {D.left c.1.1, D.right c.1.1, D.left c.1.2, D.right c.1.2})
      4 hcard p
  have havg := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => mul_le_mul_of_nonneg_left (hgeom x) (hw x))
  have hthree : (∑ x : Fin N → Bool, w x *
      (3 * (∑ v : Fin N, if x v = true then (1 : ℝ) else 0))) =
      3 * (∑ x : Fin N → Bool, w x *
        (∑ v : Fin N, if x v = true then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  simp_rw [mul_add] at havg
  rw [Finset.sum_add_distrib, hthree, he, hv, hc] at havg
  nlinarith [havg]
