-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_orbit_card_eq_card_patterns
-- name    : Geometry.KernelPatterns.orbit_card_eq_card_patterns
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:21:53.780225+00:00
-- url     : https://prove2.me/theorems/680f886c-37c5-4d13-b834-89179bb8e54a
-- title:
--   The pattern map descends to the orbit space of the `Sym(Fin m)`-action on
-- statement:
--   The pattern map descends to the orbit space of the `Sym(Fin m)`-action on
--   `n`-tuples, and identifies it with the finset of patterns.
--
--   ```lean
--   theorem Geometry.KernelPatterns.orbit_card_eq_card_patterns:
--       Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin m)) (Fin n → Fin m))
--         = (patterns n m).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Bell.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Bell.lean#L40

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

theorem Geometry.KernelPatterns.orbit_card_eq_card_patterns:
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin m)) (Fin n → Fin m))
      = (patterns n m).card := by sorry
