-- Prove2me | Theorems.Thm_Cryptography_WeilBLS_WeilPairing_pair_zero_left
-- name    : Cryptography.WeilBLS.WeilPairing.pair_zero_left
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:46:36.065955+00:00
-- url     : https://prove2.me/theorems/f5df9bee-2912-4dca-a0cf-02912ee08fe4
-- title:
--   Pair zero left
-- statement:
--   Formal statement of `Cryptography.WeilBLS.WeilPairing.pair_zero_left` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Cryptography.WeilBLS.WeilPairing.pair_zero_left(Q : torsionPoints W n) : e.pair 0 Q = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/WeilPairingBLS.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/WeilPairingBLS.lean#L57

-- Thm stub generated from Cryptography/WeilPairingBLS.lean
import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Finset.Card

/-!
# Weil pairings and the algebraic security core of BLS signatures

This development uses Mathlib's nonsingular affine points of a `WeierstrassCurve`.
A `WeilPairing` is the standard algebraic interface on the `n`-torsion subgroup:
bilinearity, alternation, image torsion, and nondegeneracy.  The BLS result is the
algebraic EUF-CMA-to-CDH reduction under the explicit fresh-message random-oracle
programming event.  Aggregate correctness and constant group-element size are also proved.
-/

open scoped BigOperators
open Finset

open Cryptography.WeilBLS

universe u v

variable {F : Type u} [Field F] [DecidableEq F]




open WeilPairing

variable {W : WeierstrassCurve F} {n : ℕ} {μ : Type v} [CommGroup μ]
    (e : WeilPairing W n μ)


@[simp]

theorem Cryptography.WeilBLS.WeilPairing.pair_zero_left(Q : torsionPoints W n) : e.pair 0 Q = 1 := by sorry
