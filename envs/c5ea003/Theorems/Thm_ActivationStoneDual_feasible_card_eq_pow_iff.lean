-- Prove2me | Theorems.Thm_ActivationStoneDual_feasible_card_eq_pow_iff
-- name    : ActivationStoneDual.feasible_card_eq_pow_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T14:57:03.072831+00:00
-- url     : https://prove2.me/theorems/23e80e4e-2bf7-4bd1-acce-8b2dae4264b2
-- title:
--   Feasible card eq pow iff
-- statement:
--   Formal statement of `ActivationStoneDual.feasible_card_eq_pow_iff` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ActivationStoneDual.feasible_card_eq_pow_iff{X : Type*} [Fintype X] {k : ℕ}
--       (a : X → Pattern k) :
--       Fintype.card (Feasible a) = 2 ^ k ↔ Function.Surjective a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ActivationStoneDual.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ActivationStoneDual.lean#L59

-- Thm stub generated from Novelty/ActivationStoneDual.lean
import Mathlib
import Definitions.Def_Novelty_ActivationStoneDual

/-!
# A finite Stone model for neural activation patterns

This file isolates the rigorous finite theorem behind the proposed Stone-duality
picture.  A network with `k` Boolean gates has an activation map
`a : X → (Fin k → Bool)`.  Its feasible Stone space is the range of `a`, not in
general the whole Boolean cube.  Hence it has at most `2^k` points, with equality
exactly when every activation pattern is feasible.

Classifiers constant on activation fibres factor uniquely through this finite
space.  Subsets of the feasible space form a Boolean algebra; their pullbacks are
exactly activation-invariant decision regions.  Finally, the full powerset concept
class on this space has VC dimension equal to its number of points.  This last
statement concerns the *full algebra of regions*, not a single fixed classifier.
-/

open Function Set
open scoped BigOperators

open ActivationStoneDual




/-
The feasible-pattern projection is onto.
-/

/-
There are exactly `2^k` formal activation patterns.
-/

/-
The finite Stone space has at most `2^k` points.
-/

/-
The commonly claimed `2^k` count is valid precisely under feasibility of
all formal activation patterns.
-/

theorem ActivationStoneDual.feasible_card_eq_pow_iff{X : Type*} [Fintype X] {k : ℕ}
    (a : X → Pattern k) :
    Fintype.card (Feasible a) = 2 ^ k ↔ Function.Surjective a := by sorry
