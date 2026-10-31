-- Prove2me | solution 1 for KServer.bernoulli_fresh_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T17:33:31.238435+00:00
-- url     : https://prove2.me/submissions/cc462666-09e6-4d42-ab2d-1a11b2ab5ad7

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (P : (ι → Bool) → ℝ) (hP : ∀ x, P x = ∏ i, if x i then p i else 1 - p i) :
    (∀ x, 0 ≤ P x) ∧ (∑ x, P x) = 1 ∧
    ∀ (i : ι) (A : (ι → Bool) → Prop) [DecidablePred A],
      (∀ x, A x → A (Function.update x i (!(x i)))) →
      (∑ x ∈ Finset.univ.filter (fun x => A x ∧ x i = true), P x) =
        p i * ∑ x ∈ Finset.univ.filter A, P x := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [hP x]
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact (hp i).1
    · exact sub_nonneg.mpr (hp i).2
  · simp_rw [hP]
    rw [← Fintype.prod_sum (fun i (b : Bool) => if b then p i else 1 - p i)]
    simp
  · intro i A _ hA
    let flip : (ι → Bool) → (ι → Bool) := fun x => Function.update x i (!(x i))
    have hinv : Function.Involutive flip := by
      intro x
      funext k
      by_cases hki : k = i
      · subst k
        simp [flip]
      · simp [flip, hki]
    have hbit (x : ι → Bool) : (flip x) i = !(x i) := by simp [flip]
    have hweight (x : ι → Bool) (hx : x i = true) :
        (1 - p i) * P x = p i * P (flip x) := by
      rw [hP x, hP (flip x)]
      rw [← Finset.mul_prod_erase Finset.univ (fun k => if x k then p k else 1 - p k)
          (Finset.mem_univ i),
        ← Finset.mul_prod_erase Finset.univ (fun k => if (flip x) k then p k else 1 - p k)
          (Finset.mem_univ i)]
      have hrest : (∏ k ∈ Finset.univ.erase i, if (flip x) k then p k else 1 - p k) =
          ∏ k ∈ Finset.univ.erase i, if x k then p k else 1 - p k := by
        apply Finset.prod_congr rfl
        intro k hk
        have hki := (Finset.mem_erase.mp hk).1
        simp [flip, hki]
      rw [hrest]
      simp only [hx, ↓reduceIte, hbit, Bool.not_true, Bool.false_eq_true]
      ring
    let T := Finset.univ.filter (fun x => A x ∧ x i = true)
    let F := Finset.univ.filter (fun x => A x ∧ x i = false)
    have hcross : (1 - p i) * (∑ x ∈ T, P x) = p i * ∑ x ∈ F, P x := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_bij (fun x _ => flip x)
      · intro x hx
        obtain ⟨_, hax, hbx⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA x hax, by simp [hbit, hbx]⟩
      · intro x _ y _ hxy
        exact hinv.injective hxy
      · intro y hy
        obtain ⟨_, hay, hby⟩ := Finset.mem_filter.mp hy
        refine ⟨flip y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA y hay, ?_⟩, hinv y⟩
        simp [hbit, hby]
      · intro x hx
        exact hweight x (Finset.mem_filter.mp hx).2.2
    have hsplit : (∑ x ∈ T, P x) + (∑ x ∈ F, P x) = ∑ x ∈ Finset.univ.filter A, P x := by
      have hh := Finset.sum_filter_add_sum_filter_not (Finset.univ.filter A)
        (fun x => x i = true) P
      simpa only [Finset.filter_filter, Bool.not_eq_true] using hh
    change (∑ x ∈ T, P x) = p i * ∑ x ∈ Finset.univ.filter A, P x
    rw [← hsplit]
    nlinarith only [hcross]
