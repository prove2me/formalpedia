-- Prove2me | Theorems.Thm_Cryptography_WeilBLS_BLSParams_aggregate_verifies
-- name    : Cryptography.WeilBLS.BLSParams.aggregate_verifies
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:46:53.903176+00:00
-- url     : https://prove2.me/theorems/caf24ce2-5188-4bb4-9458-5f206dce1a72
-- title:
--   One aggregate group element verifies a finite family of BLS signatures.
-- statement:
--   One aggregate group element verifies a finite family of BLS signatures.
--
--   ```lean
--   theorem Cryptography.WeilBLS.BLSParams.aggregate_verifies{ι : Type*} (s : Finset ι)
--       (sk : ι → ℕ) (hashPoint : ι → torsionPoints W n) :
--       P.pairing.pair (aggregate s (fun i => P.sign (sk i) (hashPoint i))) P.generator =
--         ∏ i ∈ s, P.pairing.pair (hashPoint i) (P.publicKey (sk i)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/WeilPairingBLS.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/WeilPairingBLS.lean#L232

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

theorem Cryptography.WeilBLS.BLSParams.aggregate_verifies{ι : Type*} (s : Finset ι)
    (sk : ι → ℕ) (hashPoint : ι → torsionPoints W n) :
    P.pairing.pair (aggregate s (fun i => P.sign (sk i) (hashPoint i))) P.generator =
      ∏ i ∈ s, P.pairing.pair (hashPoint i) (P.publicKey (sk i)) := by sorry
