-- Prove2me | Definitions.Def_Shared_BerggrenTQC_BraidObstruction
-- name    : Shared_BerggrenTQC_BraidObstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:30.920583+00:00
-- url     : https://prove2.me/theorems/7d85f7a3-a06a-4f93-aa5d-6b1734810ce0
-- title:
--   Aether Catalog definitions — Shared_BerggrenTQC_BraidObstruction
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.BerggrenTQC.BraidObstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/BerggrenTQC/BraidObstruction.lean by skeleton subtraction
import Mathlib

/-!
# No braid relation among the Berggren generators

The moonshot hypothesis is that the three Berggren generators braid, i.e. that
`σᵢ ↦ Bᵢ` defines a representation of an Artin braid group.  This file settles that
question in the negative and locates the obstruction precisely.

Main results.

* `braid_trace_two_two`: a general criterion.  If `X Y : Matrix (Fin 2) (Fin 2) ℤ` satisfy the
  braid relation `XYX = YXY` and have equal determinant, then
  `(tr X - tr Y) * (tr (XY) + det X) = 0`.  This is the classical `SL₂` trace criterion, proved
  here from Cayley–Hamilton in entrywise form.
* `berggren_traces`: all three Berggren lifts have trace `2`, so the trace criterion is
  *inconclusive* for them — the obstruction is not visible at the level of traces.
* `braid_fails_lift_12`, `braid_fails_lift_13`, `braid_fails_lift_23` and the corresponding
  statements `braid_fails_B₁₂`, `braid_fails_B₁₃`, `braid_fails_B₂₃` for the `3 × 3` Berggren
  matrices of the catalog: **every** pair of Berggren generators fails the braid relation.
* `berggren_mod_two`: every element of the Berggren group reduces mod `2` to either `1` or the
  swap `J = !![0,1;1,0]`.  In other words the Berggren group is contained in the *theta group*
  `Γ_θ`-type congruence condition, and carries a `ℤ/2`-valued *charge* (`charge_mul`,
  `charge_surjective`), which is abelian: the braiding statistics the tree can support are
  abelian (boson/fermion-like), never non-abelian.
* `braid_generators_not_berggren`: the standard braid pair `T = !![1,1;0,1]`,
  `L = !![1,0;-1,1]` of `SL(2,ℤ)` — the image of the Artin generators under the classical
  surjection `B₃ ↠ SL(2,ℤ)` — does satisfy the braid relation (`T_L_braid`) but **neither
  element lies in the Berggren group**.  Hence the Berggren group misses the braid generators
  of `SL(2,ℤ)` altogether.
* `berggrenGroup_ne_top`: consequently the Berggren group is a proper subgroup of `GL(2,ℤ)`.
-/

namespace BerggrenTQC

open Matrix

/-! ## The `SL₂` trace criterion for braiding -/



/-! ## The braid relations all fail -/









/-! ## The mod 2 obstruction: the Berggren group is a theta-type congruence subgroup -/

/-- Reduction of integer matrices mod `2`. -/
def redHom : Matrix (Fin 2) (Fin 2) ℤ →+* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  (Int.castRingHom (ZMod 2)).mapMatrix

/-- The mod `2` swap matrix. -/
def Jm : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 0]






/-! ## The `ℤ/2` charge of a Berggren element: abelian statistics -/

/-- The mod `2` *charge* of an integer matrix: `0` if it reduces to the identity, `1`
otherwise.  On the Berggren group this is a homomorphism to `ℤ/2` (`charge_mul`). -/
def charge (M : Matrix (Fin 2) (Fin 2) ℤ) : ZMod 2 := if redHom M = 1 then 0 else 1



/-! ## The braid generators of `SL(2,ℤ)` are not Berggren elements -/

/-- `T = !![1,1;0,1]`, the image of the first Artin generator under `B₃ ↠ SL(2,ℤ)`. -/
def Tmat : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]

/-- `L = !![1,0;-1,1]`, the image of the second Artin generator under `B₃ ↠ SL(2,ℤ)`. -/
def Lmat : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -1, 1]


/-- `T` as a unit of the matrix ring. -/
def gT : (Matrix (Fin 2) (Fin 2) ℤ)ˣ := ⟨Tmat, !![1, -1; 0, 1], by decide, by decide⟩

/-- `L` as a unit of the matrix ring. -/
def gL : (Matrix (Fin 2) (Fin 2) ℤ)ˣ := ⟨Lmat, !![1, 0; 1, 1], by decide, by decide⟩





end BerggrenTQC


