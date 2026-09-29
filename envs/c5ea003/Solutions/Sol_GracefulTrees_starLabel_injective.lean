-- Prove2me | solution 1 for GracefulTrees.starLabel_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:32:47.8967+00:00
-- url     : https://prove2.me/submissions/754d4fcb-e132-427c-8581-8152908192ca

-- Sol generated from Algebra/GracefulStars.lean
import Mathlib
import Definitions.Def_Algebra_GracefulStars
import Definitions.Def_Algebra_GracefulTrees

/-!
# Graceful labelings of stars

Stars form a basic infinite family of caterpillars.  This file proves directly that the
complete bipartite graph `K_{1,n}` is graceful.
-/

open Finset SimpleGraph
open GracefulTrees

open GracefulTrees







open GracefulTrees in
theorem solution(n : ℕ) : Function.Injective (starLabel n) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y => simp
      | inr y => simp [starLabel] at h
  | inr x =>
      cases y with
      | inl y => simp [starLabel] at h
      | inr y =>
          simp only [starLabel] at h
          exact congrArg Sum.inr (Fin.ext (by omega))
