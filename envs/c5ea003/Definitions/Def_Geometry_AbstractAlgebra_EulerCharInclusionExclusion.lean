-- Prove2me | Definitions.Def_Geometry_AbstractAlgebra_EulerCharInclusionExclusion
-- name    : Geometry_AbstractAlgebra_EulerCharInclusionExclusion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:33:35.985494+00:00
-- url     : https://prove2.me/theorems/afcfe026-7f45-4e8a-a884-68d8fcb77d9d
-- title:
--   Aether Catalog definitions — Geometry_AbstractAlgebra_EulerCharInclusionExclusion
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AbstractAlgebra.EulerCharInclusionExclusion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AbstractAlgebra/EulerCharInclusionExclusion.lean by skeleton subtraction
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic

/-!
# Two-set inclusion-exclusion for the combinatorial Euler characteristic

This file defines the combinatorial Euler characteristic of a finite set of faces
(each face being a `Finset V`) and proves the two-set inclusion-exclusion formula

`eulerChar (A ∪ B) = eulerChar A + eulerChar B - eulerChar (A ∩ B)`.

The proof relies only on `Finset.sum_union_inter`; it does not use any general
inclusion-exclusion theorem.
-/

open Finset

variable {V : Type*}

/-- The combinatorial Euler characteristic of a finite face set `X`,
defined as `∑ σ ∈ X, (-1) ^ σ.card`. -/
def eulerChar (X : Finset (Finset V)) : ℤ :=
  X.sum (fun σ => (-1 : ℤ) ^ σ.card)


