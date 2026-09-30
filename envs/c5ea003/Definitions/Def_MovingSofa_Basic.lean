-- Prove2me | Definitions.Def_MovingSofa_Basic
-- name    : MovingSofa_Basic
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-09-29T18:39:05.107611+00:00
-- url     : https://prove2.me/theorems/cbfde704-fc7e-40ac-91a6-f0e6d7afe43e
-- title:
--   Moving sofa core vocabulary
-- statement:
--   This definition bundle fixes the vocabulary for the moving sofa problem. Let $\mathbb{R}^2$ be the Euclidean plane with its standard orientation. The **hallway** is $(-\infty,1]\times[0,1]\cup[0,1]\times(-\infty,1]$, the union of its horizontal and vertical sides. A **moving sofa** is a closed connected set with a continuous motion in $E(2)$ starting at the identity and staying in the hallway. Gerver's data $r$, $x$, $y$, $p$ are given explicitly as functions of constants $A,B,\varphi,\theta$, and the sofa for those constants is the intersection of rotated hallways. The **sofa constant** is the supremum of volumes of moving sofas in $\mathbb{R}_{\ge 0}\cup\{\infty\}$. This bundle is reused by every mission theorem.\n\n**Formalization Note** Lean uses `EuclideanSpace \mathbb{R} (Fin 2)` with ASCII names (`ABphiThetaSpec`, `phi`, `theta`) and explicit constant parameters to keep the bundle independent of any existence proof.
-- source:
--   deancureton/MovingSofa@4d5569131940815f47a9ccf3e90a4c5043c56127, MovingSofaSubmission/Challenge.lean, https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofaSubmission/Challenge.lean#L1-L120

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false

/-!
# Moving sofa problem: core vocabulary

Definitions copied (with ASCII renaming + drift repair) from
`MovingSofaSubmission/Challenge.lean` in
https://github.com/deancureton/MovingSofa (Baek arXiv:2411.19826 formalization),
which itself copies `FormalConjectures/Wikipedia/MovingSofa.lean`
at `ddfbaf90f4482030d88aae5233fe933874296a23`.

ASCII renaming (platform requires conservative identifiers):
- `ABφθSpec` → `ABphiThetaSpec`
- `φ`, `θ` (chosen constants) are NOT defined here; see below.
- `r`, `x`, `y`, `p`, `gerversSofa` take explicit `(A B phi theta : ℝ)` parameters
  instead of reading the global chosen constants. This keeps this bundle
  sorry-free and independent of the `existsUnique` theorem stub (otherwise the
  bundle would import a sorry and taint every consumer with `sorryAx`).
  The mission theorems quantify over all solutions of the spec; given uniqueness,
  this implies the source statements about the chosen constants.

Drift repair vs MovingSofa pin (Lean v4.35.0-rc1, Mathlib v4.35):
- Workspace pin is the supported Prove2Me rev `c5ea003` (Lean v4.30.0).
- `rigidMotionTopology`: original induces from `ℝ² →ᴬ[ℝ] ℝ²`, whose
  `TopologicalSpace` instance exists in v4.35 but not in v4.30.
  Here we induce from `C(ℝ², ℝ²)` via `toContinuousMap`, which exists in both.
-/

noncomputable section

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

/-- The plane `ℝ²` with the orientation of its standard basis. -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Module.Basis.orientation <| PiLp.basisFun 2 _ _⟩

/-- The plane `ℝ²` has dimension two. -/
instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry
open MeasureTheory
open scoped ENNReal

/-- The horizontal side of the hallway. -/
def horizontalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

/-- The vertical side of the hallway. -/
def verticalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

/-- The hallway is the union of its horizontal and vertical sides. -/
def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

/-- The topology on the isometry group `E(2)` (drift-repaired, see header). -/
instance rigidMotionTopology : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap.toContinuousMap) inferInstance

/-- A moving sofa structure. -/
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

/-- Rotation then translation. -/
def rotateTranslate (α : Real.Angle) (p : ℝ²) : E(2) :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans
    (EuclideanGeometry.o.rotation α).toAffineIsometryEquiv

/-- Sofa from rotation path. -/
def sofaOfRotateTranslatePath (p : ℝ → ℝ²) : Set ℝ² :=
  rotateTranslate 0 (p 0) '' horizontalHallway ∩
  rotateTranslate ↑(π / 2) (p (π / 2)) '' verticalHallway ∩
  ⋂ α ∈ Set.Icc 0 (π / 2), rotateTranslate α (p α) '' hallway

namespace GerversSofa

/-- Eq. 1-4 of Romik 2018 specifying Gerver's constants (ASCII name). -/
def ABphiThetaSpec (A B phi theta : ℝ) : Prop :=
  0 ≤ phi ∧ phi ≤ theta ∧ theta ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (theta.cos - phi.cos) - 2 * B * phi.sin
    + (theta - phi - 1) * theta.cos - theta.sin + phi.cos + phi.sin = 0 ∧
  A * (3 * theta.sin + phi.sin) - 2 * B * phi.cos
    + 3 * (theta - phi - 1) * theta.sin + 3 * theta.cos - phi.sin + phi.cos = 0 ∧
  A * phi.cos - (phi.sin + 1 / 2 - phi.cos / 2 + B * phi.sin) = 0 ∧
  (A + π / 2 - phi - theta) - (B - (theta - phi) * (1 + A) / 2 - (theta - phi)^2 / 4) = 0

/-- Piecewise `r` function, explicit in the constants. -/
def r (A B phi theta α : ℝ) : ℝ :=
  if α ≤ phi then
    1 / 2
  else if α ≤ theta then
    (1 + A + α - phi) / 2
  else if α ≤ π / 2 - theta then
    A + α - phi
  else if α ≤ π / 2 - phi then
    B - (π / 2 - α - phi) * (1 + A) / 2 - (π / 2 - α - phi) ^ 2 / 4
  else
    0

/-- `y` integral, explicit in the constants. -/
def y (A B phi theta α : ℝ) : ℝ :=
  ∫ t in α..π / 2 - phi, r A B phi theta t * t.sin

/-- `x` integral, explicit in the constants. -/
def x (A B phi theta α : ℝ) : ℝ :=
  1 - ∫ t in α..π / 2 - phi, r A B phi theta t * t.cos

/-- Rotation path of Gerver's sofa, explicit in the constants. -/
def p (A B phi theta α : ℝ) : ℝ² :=
  !₂[if α ≤ phi
      then α.cos - 1
      else x A B phi theta (π / 2 - α) * α.cos + y A B phi theta (π / 2 - α) * α.sin - 1,
    if α ≤ π / 2 - phi
      then y A B phi theta α * α.cos - (4 * x A B phi theta 0 - 2 - x A B phi theta α) * α.sin - 1
      else -(4 * x A B phi theta 0 - 3) * α.sin - 1]

end GerversSofa

/-- Gerver's sofa for explicit constants. -/
def gerversSofaWith (A B phi theta : ℝ) : Set ℝ² :=
  sofaOfRotateTranslatePath (GerversSofa.p A B phi theta)

/-- The sofa constant: supremum of areas of moving sofas. -/
def sofaConstant : ℝ≥0∞ := ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s

end MovingSofa


