-- Prove2me | solution 1 for GracefulTrees.pathGraph_isGraceful
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:32:47.154914+00:00
-- url     : https://prove2.me/submissions/b7475521-951c-4ded-b459-0d902ec74b4b

-- Sol generated from Algebra/GracefulTrees.lean
import Mathlib
import Definitions.Def_Algebra_GracefulTrees
import Theorems.Thm_GracefulTrees_pathLabel_consecutive
import Theorems.Thm_GracefulTrees_pathLabel_injective

/-!
# Graceful labelings of paths and their decomposition connection

The Graceful Tree Conjecture is open.  This file formalizes the standard notion and proves
an infinite established case: every finite path is graceful.  It also proves the elementary
counting theorem used when graceful copies partition the edges of a complete graph.
-/

open Finset SimpleGraph

open GracefulTrees




/-- Every alternating path label lies between zero and `n`. -/
theorem pathLabel_le (n : ℕ) (i : Fin (n + 1)) : pathLabel n i ≤ n := by
  unfold pathLabel
  split_ifs <;> omega








open GracefulTrees in
theorem solution(n : ℕ) :
    IsGraceful (pathGraph (n + 1)) n (pathLabel n) := by
  refine ⟨pathLabel_injective n, pathLabel_le n, ?_, ?_⟩
  · intro u v huv
    rw [pathGraph_adj] at huv
    rcases huv with huv | hvu
    · have hi : u.1 + 1 < n + 1 := by omega
      have hv : v = ⟨u.1 + 1, hi⟩ := Fin.ext huv.symm
      subst v
      rw [pathLabel_consecutive n u hi, Finset.mem_Icc]
      omega
    · have hi : v.1 + 1 < n + 1 := by omega
      have hu : u = ⟨v.1 + 1, hi⟩ := Fin.ext hvu.symm
      subst u
      rw [Nat.dist_comm, pathLabel_consecutive n v hi, Finset.mem_Icc]
      omega
  · intro d hd
    rw [Finset.mem_Icc] at hd
    let i : Fin (n + 1) := ⟨n - d, by omega⟩
    have hi : i.1 + 1 < n + 1 := by simp [i]; omega
    refine ⟨i, ⟨i.1 + 1, hi⟩, ?_, ?_⟩
    · rw [pathGraph_adj]
      exact Or.inl rfl
    · rw [pathLabel_consecutive n i hi]
      simp [i]
      omega
