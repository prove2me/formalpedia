-- Prove2me | solution 1 for Geometry.KernelPatterns.bell_eq_sum_stirlingSecond
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:45:34.211203+00:00
-- url     : https://prove2.me/submissions/15e4573a-bc7d-4b2c-8f4a-b7b940b0959b

-- Sol generated from Geometry/KernelPatterns/Synthesis.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_BellRecursion
import Definitions.Def_Geometry_KernelPatterns_BraidFlats
import Definitions.Def_Geometry_KernelPatterns_Core
import Theorems.Thm_Geometry_KernelPatterns_card_patterns_eq_bell
import Theorems.Thm_Geometry_KernelPatterns_card_patterns_eq_sum_stirlingSecond

/-!
# Synthesis: one classification theorem, four counting corollaries

The three strands of `Geometry.KernelPatterns` meet here.

* Algebraic: kernel patterns classify the orbits of the diagonal symmetric
  group action (`orbit_card_eq_bell`).
* Combinatorial: they are the set partitions, counted with `k` blocks by the
  Stirling numbers and in total by the Bell numbers, giving the classical
  identity `bell n = Σ_k S(n,k)` (`bell_eq_sum_stirlingSecond`) — both sides of
  which are Mathlib definitions given purely by recursions.
* Geometric: they are the flats of the braid arrangement in `ℝ^n`, so the
  intersection lattice of the braid arrangement has `Nat.bell n` elements
  (`card_braidFlats_eq_bell`).
-/

open Geometry.KernelPatterns

open Finset







open Geometry.KernelPatterns in
theorem solution(n : ℕ) :
    Nat.bell n = ∑ k ∈ range (n + 1), Nat.stirlingSecond n k := by
  rw [← card_patterns_eq_sum_stirlingSecond, card_patterns_eq_bell]
