-- Prove2me | solution 1 for GracefulTrees.pathLabel_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:29:42.060483+00:00
-- url     : https://prove2.me/submissions/baae0826-4744-428b-9c9e-7babd371cb0b

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
theorem solution(n : ℕ) : Function.Injective (pathLabel n) := by
  intro i j hij
  rw [pathLabel, pathLabel] at hij
  rcases Nat.even_or_odd i.1 with ⟨ki, hki⟩ | ⟨ki, hki⟩ <;>
  rcases Nat.even_or_odd j.1 with ⟨kj, hkj⟩ | ⟨kj, hkj⟩ <;>
  simp_all
  · -- both even
    omega
  · -- i even, j odd
    omega
  · -- i odd, j even
    omega
  · -- both odd
    omega
