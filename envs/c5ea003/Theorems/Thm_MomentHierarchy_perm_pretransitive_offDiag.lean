-- Prove2me | Theorems.Thm_MomentHierarchy_perm_pretransitive_offDiag
-- name    : MomentHierarchy.perm_pretransitive_offDiag
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:38:15.59945+00:00
-- url     : https://prove2.me/theorems/ef9830a0-56a2-4169-a61e-1cee998aafce
-- title:
--   The natural action of the full symmetric group on ordered pairs of distinct points is
-- statement:
--   The natural action of the full symmetric group on ordered pairs of distinct points is
--   transitive: given `a ≠ b` and `c ≠ d`, the product of two transpositions moves `(a, b)`
--   to `(c, d)`.
--
--   ```lean
--   theorem MomentHierarchy.perm_pretransitive_offDiag:
--       IsPretransitive (Equiv.Perm X) (offDiagSub (Equiv.Perm X) X) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/MomentHierarchyBell.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/MomentHierarchyBell.lean#L28

-- Thm stub generated from Logic/MomentHierarchyBell.lean
import Mathlib
import Definitions.Def_Logic_MomentHierarchy
import Definitions.Def_Logic_MomentHierarchyBell

/-!
# The Burnside Moment Hierarchy, part II: symmetric groups, kernels and Bell numbers

This file continues `Logic.MomentHierarchy`. Instantiating the moment identity
`∑_{g ∈ G} |X^g|^k = #((X^k)/G) · |G|` at the full symmetric group `Sym X` turns the
hierarchy into the moment sequence of the number of fixed points of a uniformly random
permutation. The orbits of `Sym X` on `k`-tuples are classified by kernel partitions, so
for `k ≤ |X|` the `k`-th level counts set partitions of a `k`-element set, and the
Cauchy–Schwarz inequality of part I becomes log-convexity of the Bell sequence.
-/

open MulAction Finset

open MomentHierarchy

/-! ## Cycle 4: instantiation at the symmetric group

For the natural action of `Equiv.Perm X` on a finite `X` the hierarchy becomes the
moment sequence of the number of fixed points of a uniformly random permutation. The
action is transitive and 2-transitive, so the first two moments are `1` and `2` — the
first two Bell numbers, i.e. the first two moments of a Poisson(1) variable. -/


variable (X : Type*) [Fintype X] [DecidableEq X]

theorem MomentHierarchy.perm_pretransitive_offDiag:
    IsPretransitive (Equiv.Perm X) (offDiagSub (Equiv.Perm X) X) := by sorry
