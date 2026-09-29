-- Prove2me | Definitions.Def_Tropical_TropicalAlgebra_TropicalLineCounting
-- name    : Tropical_TropicalAlgebra_TropicalLineCounting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:11.356131+00:00
-- url     : https://prove2.me/theorems/8ecc783e-89b9-4e60-a650-a6b8a73d6c19
-- title:
--   Aether Catalog definitions — Tropical_TropicalAlgebra_TropicalLineCounting
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.TropicalAlgebra.TropicalLineCounting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/TropicalAlgebra/TropicalLineCounting.lean by skeleton subtraction
import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
/-
# Tropical Line Counting (degree 1)

This file develops the most basic case of tropical curve counting: the
degree-1 tropical line in the plane, its three primitive edge directions,
the balancing condition, the vertex multiplicity, and the tropical–classical
correspondence that determines the (unique) vertex of a tropical line passing
through two generic points.

Note on imports: the prompt requested `Mathlib.Data.Matrix.Det`, which does not
exist in this Mathlib version.  We use `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`
instead, which provides `Matrix.det_fin_two`.
-/

/-- First primitive edge direction of the degree-1 tropical line. -/
def e1 : Fin 2 → ℤ := ![1, 0]

/-- Second primitive edge direction of the degree-1 tropical line. -/
def e2 : Fin 2 → ℤ := ![0, 1]

/-- Third primitive edge direction of the degree-1 tropical line. -/
def e3 : Fin 2 → ℤ := ![-1, -1]


/-- The matrix whose columns are the two outgoing edge directions `e1`, `e2`
at the vertex of the tropical line. -/
def edgeMatrix : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![e1 0, e2 0], ![e1 1, e2 1]]

/-- The vertex multiplicity is the absolute value of the determinant of the
edge matrix. -/
def vertexMultiplicity : ℤ := |edgeMatrix.det|


/-- Two points are *generic* if their difference is not parallel to any of the
primitive edge directions `e1`, `e2`, `e3`. -/
def IsGenericPoints (p1 p2 : Fin 2 → ℤ) : Prop :=
  ∀ (i : Fin 3) (j : Fin 3), i ≠ j →
    ¬(∃ t : ℤ, p2 - p1 = t • ![e1, e2, e3] i)


