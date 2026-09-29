-- Prove2me | solution 1 for Cryptography.WeilBLS.BLSParams.aggregate_verifies
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:30:44.398166+00:00
-- url     : https://prove2.me/submissions/48bcc7bc-cbd7-4608-88a4-9c83a46d4a95

-- Sol generated from Cryptography/WeilPairingBLS.lean
import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Theorems.Thm_Cryptography_WeilBLS_WeilPairing_bilinear_left
import Theorems.Thm_Cryptography_WeilBLS_WeilPairing_bilinear_right
import Theorems.Thm_Cryptography_WeilBLS_WeilPairing_pair_add_left
import Theorems.Thm_Cryptography_WeilBLS_WeilPairing_pair_zero_left
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




/-- Correctness of BLS verification follows from Weil bilinearity. -/
theorem verifies_sign (sk : ℕ) (hashPoint : torsionPoints W n) :
    P.verifies (P.publicKey sk) hashPoint (P.sign sk hashPoint) := by
  unfold verifies publicKey sign
  rw [P.pairing.bilinear_left, P.pairing.bilinear_right]









/-- Pairing an aggregate equals the product of individual pairings. -/
theorem pair_aggregate {ι : Type*} (s : Finset ι)
    (signature : ι → torsionPoints W n) :
    P.pairing.pair (aggregate s signature) P.generator =
      ∏ i ∈ s, P.pairing.pair (signature i) P.generator := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [aggregate]
  | @insert a s ha ih =>
      simp only [aggregate, sum_insert ha, prod_insert ha]
      rw [P.pairing.pair_add_left]
      exact congrArg (fun x => P.pairing.pair (signature a) P.generator * x)
        (by simpa only [aggregate] using ih)





namespace Cryptography.WeilBLS.BLSParams
/-- Pairing an aggregate equals the product of individual pairings. -/
theorem pair_aggregate {ι : Type*} (s : Finset ι)
    (signature : ι → torsionPoints W n) :
    P.pairing.pair (aggregate s signature) P.generator =
      ∏ i ∈ s, P.pairing.pair (signature i) P.generator := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [aggregate]
  | @insert a s ha ih =>
      simp only [aggregate, sum_insert ha, prod_insert ha]
      rw [P.pairing.pair_add_left]
      exact congrArg (fun x => P.pairing.pair (signature a) P.generator * x)
        (by simpa only [aggregate] using ih)

end Cryptography.WeilBLS.BLSParams

namespace Cryptography.WeilBLS.BLSParams
/-- Correctness of BLS verification follows from Weil bilinearity. -/
theorem verifies_sign (sk : ℕ) (hashPoint : torsionPoints W n) :
    P.verifies (P.publicKey sk) hashPoint (P.sign sk hashPoint) := by
  unfold verifies publicKey sign
  rw [P.pairing.bilinear_left, P.pairing.bilinear_right]

end Cryptography.WeilBLS.BLSParams

open Cryptography.WeilBLS in
theorem solution{ι : Type*} (s : Finset ι)
    (sk : ι → ℕ) (hashPoint : ι → torsionPoints W n) :
    P.pairing.pair (aggregate s (fun i => P.sign (sk i) (hashPoint i))) P.generator =
      ∏ i ∈ s, P.pairing.pair (hashPoint i) (P.publicKey (sk i)) := by
  rw [P.pair_aggregate]
  apply Finset.prod_congr rfl
  intro i hi
  exact P.verifies_sign (sk i) (hashPoint i)
