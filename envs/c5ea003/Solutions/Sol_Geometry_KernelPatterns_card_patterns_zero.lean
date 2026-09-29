-- Prove2me | solution 1 for Geometry.KernelPatterns.card_patterns_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:30:59.852628+00:00
-- url     : https://prove2.me/submissions/700f9d8c-5a8b-4b5e-8730-3eb2c31b8275

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


/-- `patterns n n` is the finset of idempotent tuples. -/
theorem patterns_self_eq_filter (n : ℕ) :
    patterns n n = univ.filter fun p : Fin n → Fin n => pat p = p := by
  ext p
  simp [mem_patterns_self]

/-! ### Orbit counting -/


variable (n m : ℕ)



/-! ### Patterns are set partitions -/



/-! ### Refining the count by the number of blocks -/


/-! ### The Bell numbers `1, 1, 2, 5, 15, 52` -/













open Geometry.KernelPatterns in
theorem solution: (patterns 0 0).card = 1 := by
  rw [patterns_self_eq_filter]; decide
