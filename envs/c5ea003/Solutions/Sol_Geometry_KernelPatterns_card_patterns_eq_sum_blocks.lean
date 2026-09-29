-- Prove2me | solution 1 for Geometry.KernelPatterns.card_patterns_eq_sum_blocks
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:41:19.003788+00:00
-- url     : https://prove2.me/submissions/e41af8d0-411e-4907-b8ce-8a176b7429c4

-- Sol generated from Geometry/KernelPatterns/Bell.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core

/-!
# Counting kernel patterns: orbits, set partitions and the Bell numbers

Building on `Geometry.KernelPatterns.Core`, this file counts kernel patterns.

* `orbit_card_eq_card_patterns` — the number of `Sym(Fin m)`-orbits on the
  configuration space `(Fin m)^n` of `n`-tuples equals `(patterns n m).card`.
  (This is the counting form of the completeness theorem `perm_orbit_iff_pat_eq`.)
* `patternsEquivSetoid` — kernel patterns of length `n` are in bijection with
  equivalence relations (i.e. set partitions) on `Fin n`.
* `card_patterns_le_five` — the first six values of the pattern-counting
  sequence are the Bell numbers `1, 1, 2, 5, 15, 52` (OEIS A000110), agreeing
  with Mathlib's `Nat.bell`.
* `card_patterns_eq_sum_blocks` — the refinement of the count by the number of
  blocks.
-/

open Geometry.KernelPatterns

open Finset



/-! ### Orbit counting -/


variable (n m : ℕ)



/-! ### Patterns are set partitions -/



/-! ### Refining the count by the number of blocks -/


/-! ### The Bell numbers `1, 1, 2, 5, 15, 52` -/













open Geometry.KernelPatterns in
theorem solution(n : ℕ) :
    (patterns n n).card = ∑ k ∈ range (n + 1), (patternsWith n k).card := by
  classical
  refine Finset.card_eq_sum_card_fiberwise (f := fun p => (univ.image p).card) ?_
  intro p _
  have : (univ.image p).card ≤ n := by simpa using Finset.card_le_univ (univ.image p)
  simpa [Nat.lt_succ_iff] using this
