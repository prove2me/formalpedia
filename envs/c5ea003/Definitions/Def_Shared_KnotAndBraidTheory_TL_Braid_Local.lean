-- Prove2me | Definitions.Def_Shared_KnotAndBraidTheory_TL_Braid_Local
-- name    : Shared_KnotAndBraidTheory_TL_Braid_Local
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:02:23.062913+00:00
-- url     : https://prove2.me/theorems/87788ef1-a5ca-4c49-b847-20dcbef43487
-- title:
--   Aether Catalog definitions — Shared_KnotAndBraidTheory_TL_Braid_Local
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.KnotAndBraidTheory.TL.Braid.Local`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/KnotAndBraidTheory/TL_Braid_Local.lean by skeleton subtraction
import Mathlib

/-!
# Local Temperley–Lieb / Jones braid identity

This file gives a minimal, self-contained formalization of the *local* Jones braid
relation built from a single Temperley–Lieb idempotent-like generator together with a
unit parameter `q`.

Let `R` be a commutative ring and `A` a (possibly noncommutative) unital `R`-algebra.
Given a unit `q : Rˣ`, set the loop parameter `δ = -(q + q⁻¹)` and define the Jones
braid generators
`jonesGen q e = q + e`, `jonesGenInv q e = q⁻¹ + e`
(where scalars are mapped into `A` via `algebraMap`).

If `e, f : A` satisfy the local Temperley–Lieb relations
`e² = δ e`, `f² = δ f`, `e f e = e`, `f e f = f`,
then the braid relation
`jonesGen q e * jonesGen q f * jonesGen q e = jonesGen q f * jonesGen q e * jonesGen q f`
holds, and each `jonesGen q e` is a unit with inverse `jonesGenInv q e`.
-/

namespace TLBraidLocal

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-- The Temperley–Lieb loop parameter `δ = -(q + q⁻¹)` associated to a unit `q`. -/
def tlLoop (q : Rˣ) : R := -((q : R) + ((q⁻¹ : Rˣ) : R))

/-- The Jones braid generator `q + e`. -/
def jonesGen (q : Rˣ) (e : A) : A := algebraMap R A (q : R) + e

/-- The inverse Jones braid generator `q⁻¹ + e`. -/
def jonesGenInv (q : Rˣ) (e : A) : A := algebraMap R A ((q⁻¹ : Rˣ) : R) + e







end TLBraidLocal


