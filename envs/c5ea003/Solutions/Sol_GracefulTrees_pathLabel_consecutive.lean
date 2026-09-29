-- Prove2me | solution 1 for GracefulTrees.pathLabel_consecutive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:29:41.401495+00:00
-- url     : https://prove2.me/submissions/5ae0c1f4-db98-4fe6-8bfd-f3ab24753d44

-- Sol generated from Algebra/GracefulTrees.lean
import Mathlib
import Definitions.Def_Algebra_GracefulTrees

/-!
# Graceful labelings of paths and their decomposition connection

The Graceful Tree Conjecture is open.  This file formalizes the standard notion and proves
an infinite established case: every finite path is graceful.  It also proves the elementary
counting theorem used when graceful copies partition the edges of a complete graph.
-/

open Finset SimpleGraph

open GracefulTrees












open GracefulTrees in
theorem solution(n : ℕ) (i : Fin (n + 1)) (hi : i.1 + 1 < n + 1) :
    Nat.dist (pathLabel n i) (pathLabel n ⟨i.1 + 1, hi⟩) = n - i.1 := by
  unfold pathLabel
  by_cases heven : Even i.1
  · -- i is even, so i+1 is odd
    have hodd : ¬Even (i.1 + 1) := by simp [heven, parity_simps]
    simp [heven, hodd]
    obtain ⟨k, hk⟩ := heven
    have hi2 : (i.1 + 1) / 2 = i.1 / 2 := by omega
    rw [hi2]
    simp [Nat.dist]
    omega
  · -- i is odd, so i+1 is even
    have heven_succ : Even (i.1 + 1) := by simp [heven, parity_simps]
    simp [heven, heven_succ]
    obtain ⟨k, hk⟩ := heven_succ
    simp [Nat.dist]
    omega
