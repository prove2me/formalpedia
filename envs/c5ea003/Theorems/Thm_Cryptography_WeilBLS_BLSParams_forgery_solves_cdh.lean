-- Prove2me | Theorems.Thm_Cryptography_WeilBLS_BLSParams_forgery_solves_cdh
-- name    : Cryptography.WeilBLS.BLSParams.forgery_solves_cdh
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:47:03.792872+00:00
-- url     : https://prove2.me/theorems/2aef5703-6685-4d9d-bef8-cc265d4037c8
-- title:
--   Algebraic EUF-CMA-to-CDH reduction.
-- statement:
--   **Algebraic EUF-CMA-to-CDH reduction.** Under fresh-message oracle programming,
--   every valid BLS forgery is the CDH solution.
--
--   ```lean
--   theorem Cryptography.WeilBLS.BLSParams.forgery_solves_cdh{Message : Type*} [DecidableEq Message]
--       (game : ProgrammedFreshChallenge P Message)
--       (forgedSignature : torsionPoints W n)
--       (valid : P.verifies game.challenge.publicA
--         (game.hashToCurve game.targetMessage) forgedSignature) :
--       forgedSignature = game.challenge.target := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/WeilPairingBLS.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/WeilPairingBLS.lean#L183

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












/-! ## BLS signatures and CDH reduction -/


variable {W : WeierstrassCurve F} {n : ℕ} {μ : Type v} [CommGroup μ]


open BLSParams

variable (P : BLSParams W n μ)

theorem Cryptography.WeilBLS.BLSParams.forgery_solves_cdh{Message : Type*} [DecidableEq Message]
    (game : ProgrammedFreshChallenge P Message)
    (forgedSignature : torsionPoints W n)
    (valid : P.verifies game.challenge.publicA
      (game.hashToCurve game.targetMessage) forgedSignature) :
    forgedSignature = game.challenge.target := by sorry
