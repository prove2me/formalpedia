-- Prove2me | Theorems.Thm_Cryptography_WeilBLS_WeilPairing_pair_add_left
-- name    : Cryptography.WeilBLS.WeilPairing.pair_add_left
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:46:30.120296+00:00
-- url     : https://prove2.me/theorems/c1d060b1-ead2-4936-b56d-91c6514d784d
-- title:
--   Additivity in the first argument.
-- statement:
--   Additivity in the first argument.
--
--   ```lean
--   theorem Cryptography.WeilBLS.WeilPairing.pair_add_left(P Q R : torsionPoints W n) :
--       e.pair (P + Q) R = e.pair P R * e.pair Q R := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/WeilPairingBLS.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/WeilPairingBLS.lean#L65

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

theorem Cryptography.WeilBLS.WeilPairing.pair_add_left(P Q R : torsionPoints W n) :
    e.pair (P + Q) R = e.pair P R * e.pair Q R := by sorry
