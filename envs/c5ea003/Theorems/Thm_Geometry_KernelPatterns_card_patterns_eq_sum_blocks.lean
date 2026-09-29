-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_card_patterns_eq_sum_blocks
-- name    : Geometry.KernelPatterns.card_patterns_eq_sum_blocks
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:19:15.182125+00:00
-- url     : https://prove2.me/theorems/331c9b2f-2e27-4de6-90b9-2de9e3301742
-- title:
--   Card patterns eq sum blocks
-- statement:
--   Formal statement of `Geometry.KernelPatterns.card_patterns_eq_sum_blocks` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Geometry.KernelPatterns.card_patterns_eq_sum_blocks(n : ℕ) :
--       (patterns n n).card = ∑ k ∈ range (n + 1), (patternsWith n k).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Bell.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Bell.lean#L110

-- Thm stub generated from Geometry/KernelPatterns/Bell.lean
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

theorem Geometry.KernelPatterns.card_patterns_eq_sum_blocks(n : ℕ) :
    (patterns n n).card = ∑ k ∈ range (n + 1), (patternsWith n k).card := by sorry
