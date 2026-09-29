-- Prove2me | solution 1 for GracefulTrees.starGraph_isGraceful
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:34:06.00516+00:00
-- url     : https://prove2.me/submissions/322bcade-3004-4eac-adb3-389f627fe87a

-- Sol generated from Algebra/GracefulStars.lean
import Mathlib
import Definitions.Def_Algebra_GracefulStars
import Definitions.Def_Algebra_GracefulTrees
import Theorems.Thm_GracefulTrees_starLabel_injective

/-!
# Graceful labelings of stars

Stars form a basic infinite family of caterpillars.  This file proves directly that the
complete bipartite graph `K_{1,n}` is graceful.
-/

open Finset SimpleGraph
open GracefulTrees

open GracefulTrees



/-- Every star label lies in `0,…,n`. -/
theorem starLabel_le (n : ℕ) (v : Unit ⊕ Fin n) : starLabel n v ≤ n := by
  cases v <;> simp [starLabel]




open GracefulTrees in
theorem solution(n : ℕ) :
    IsGraceful (completeBipartiteGraph Unit (Fin n)) n (starLabel n) := by
  refine ⟨starLabel_injective n, starLabel_le n, ?_, ?_⟩
  · intro u v huv
    rw [completeBipartiteGraph_adj] at huv
    rcases huv with huv | huv
    · cases u with
      | inl u =>
          cases v with
          | inl v => simp at huv
          | inr v =>
              simp only [starLabel, Nat.dist_zero_left, Finset.mem_Icc]
              omega
      | inr u => simp at huv
    · cases u with
      | inl u => simp at huv
      | inr u =>
          cases v with
          | inl v =>
              simp only [starLabel, Nat.dist_zero_right, Finset.mem_Icc]
              omega
          | inr v => simp at huv
  · intro d hd
    rw [Finset.mem_Icc] at hd
    let i : Fin n := ⟨d - 1, by omega⟩
    refine ⟨Sum.inl (), Sum.inr i, ?_, ?_⟩
    · simp [completeBipartiteGraph_adj]
    · simp only [starLabel, Nat.dist_zero_left]
      simp [i]
      omega
