-- Prove2me | solution 1 for mme_recursive_thin_split_marginal_joint_counts
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-11T22:14:32.460163+00:00
-- url     : https://prove2.me/submissions/8ec61cad-7ab3-4c27-ae71-a230e6c22b99

import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Theorems.Thm_mme_recursive_thin_split_marginals_unique

open BigOperators MME.RecursiveThinSplit

set_option autoImplicit false

private theorem count_map {A I : Type*} [Fintype A] [DecidableEq A] [DecidableEq I]
    {n : ℕ} (w : Fin n → A) (coord : A → I) (j : I) :
    count (fun t ↦ coord (w t)) j =
      ∑ a : {a // coord a = j}, count w a.val := by
  classical
  let s := Finset.univ.filter (fun a : A ↦ coord a = j)
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n)) s w
  have hsub := Finset.sum_subtype (F := inferInstance) s
    (fun a ↦ show a ∈ s ↔ coord a = j by simp [s]) (count w)
  rw [← hsub]
  simpa [count, s] using h.symm

private theorem cast_marginal (half : ℕ) (parent : Fin 3 → ℕ)
    (m : Split half parent → ℕ) (i : Fin 3) (j : Fin (half + 1)) :
    mme_modern_marginal (fun a ↦ a.val i) (fun a ↦ (m a : ℝ)) j =
      ((∑ a : {a : Split half parent // a.val i = j}, m a.val : ℕ) : ℝ) := by
  simp [mme_modern_marginal]

theorem solution (half : ℕ) (parent : Fin 3 → ℕ)
    (hthin : ∃ i, parent i ≤ 1) (n : ℕ) (m : Split half parent → ℕ) :
    (∀ w : Fin n → Split half parent, HasMarginalCounts w m ↔ HasJointCounts w m) ∧
      Nat.card {w : Fin n → Split half parent // HasMarginalCounts w m} =
        Nat.card {w : Fin n → Split half parent // HasJointCounts w m} := by
  classical
  have heq (w : Fin n → Split half parent) :
      HasMarginalCounts w m ↔ HasJointCounts w m := by
    constructor
    · intro h
      have same : (fun a ↦ (count w a : ℝ)) = (fun a ↦ (m a : ℝ)) := by
        apply mme_recursive_thin_split_marginals_unique half parent hthin
        intro i j
        rw [cast_marginal, cast_marginal,
          ← count_map w (fun a ↦ a.val i) j, h i j]
      intro a
      exact_mod_cast congrFun same a
    · intro h i j
      rw [count_map w (fun a ↦ a.val i) j]
      apply Finset.sum_congr rfl
      intro a _
      exact h a.val
  refine ⟨heq, ?_⟩
  have hp : (fun w : Fin n → Split half parent ↦ HasMarginalCounts w m) =
      (fun w ↦ HasJointCounts w m) := funext (fun w ↦ propext (heq w))
  rw [hp]
