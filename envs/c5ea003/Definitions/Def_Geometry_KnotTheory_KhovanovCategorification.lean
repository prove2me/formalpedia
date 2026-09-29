-- Prove2me | Definitions.Def_Geometry_KnotTheory_KhovanovCategorification
-- name    : Geometry_KnotTheory_KhovanovCategorification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:40:13.635197+00:00
-- url     : https://prove2.me/theorems/3642fe17-2fa0-4402-8e01-ab1c616a0325
-- title:
--   Aether Catalog definitions — Geometry_KnotTheory_KhovanovCategorification
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KnotTheory.KhovanovCategorification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KnotTheory/KhovanovCategorification.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_KnotTheory_Defs
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/

/-!
# The graded Euler state sum underlying Khovanov homology

This file formalizes the decategorification calculation for an arbitrary link
diagram.  A Khovanov generator consists of a smoothing state together with a
choice of one of the two quantum basis vectors on every resulting circle.  The
main theorem proves that the graded Euler sum of these generators is the
corresponding Jones state sum.
-/

namespace Knot.Khovanov

open Finset LaurentPolynomial

/-- A Khovanov cube generator is a smoothing state and a binary enhancement of
all circles in that smoothing.  `true` denotes the basis vector of degree `1`
and `false` the basis vector of degree `-1`. -/
abbrev Generator {n : ℕ} (D : Knot.LinkDiagram n) :=
  Σ s : Knot.KState n, Fin (D.loops s) → Bool

/-- The quantum degree contributed by the circle labels of an enhancement. -/
def enhancementDegree {m : ℕ} (e : Fin m → Bool) : ℤ :=
  ∑ i, if e i then 1 else -1

/-- The homological degree of a cube generator is its number of `B`-smoothings. -/
def homologicalDegree {n : ℕ} {D : Knot.LinkDiagram n} (g : Generator D) : ℕ :=
  Knot.numB g.1

/-- The quantum degree is the smoothing shift plus the degrees of all enhanced
circles. -/
def quantumDegree {n : ℕ} {D : Knot.LinkDiagram n} (g : Generator D) : ℤ :=
  (Knot.numA g.1 : ℤ) - (Knot.numB g.1 : ℤ) + enhancementDegree g.2

/-- The graded Euler sum of the Khovanov cube generators. -/
noncomputable def gradedEulerCharacteristic {n : ℕ} (D : Knot.LinkDiagram n) :
    LaurentPolynomial ℤ :=
  ∑ g : Generator D, (-1 : LaurentPolynomial ℤ) ^ homologicalDegree g * T (quantumDegree g)

/-- The Jones state sum in the normalization naturally produced by the
Khovanov cube: each smoothing circle contributes `q + q⁻¹`. -/
noncomputable def jonesStateSum {n : ℕ} (D : Knot.LinkDiagram n) :
    LaurentPolynomial ℤ :=
  ∑ s : Knot.KState n,
    (-1 : LaurentPolynomial ℤ) ^ Knot.numB s *
      T ((Knot.numA s : ℤ) - (Knot.numB s : ℤ)) *
      (T 1 + T (-1)) ^ D.loops s

/-- Splitting off the label of the first circle identifies enhancements of
`m + 1` circles with a label and an enhancement of `m` circles. -/
def enhancementSuccEquiv (m : ℕ) :
    (Fin (m + 1) → Bool) ≃ Bool × (Fin m → Bool) where
  toFun e := (e 0, fun i => e i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv e := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv p := by
    cases p
    rfl




/-- The writhe-normalized graded Euler characteristic of an oriented diagram. -/
noncomputable def orientedGradedEulerCharacteristic {n : ℕ}
    (D : Knot.OrientedLinkDiagram n) : LaurentPolynomial ℤ :=
  T (-3 * D.writhe) * gradedEulerCharacteristic D.toLinkDiagram

/-- The writhe-normalized Jones state sum of an oriented diagram. -/
noncomputable def orientedJonesStateSum {n : ℕ}
    (D : Knot.OrientedLinkDiagram n) : LaurentPolynomial ℤ :=
  T (-3 * D.writhe) * jonesStateSum D.toLinkDiagram



end Knot.Khovanov


