-- Prove2me | Definitions.Def_Geometry_Stereographic_FixedPointFoundations
-- name    : Geometry_Stereographic_FixedPointFoundations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:58.392819+00:00
-- url     : https://prove2.me/theorems/9385f43a-7146-45dc-b193-95867a14d479
-- title:
--   Aether Catalog definitions — Geometry_Stereographic_FixedPointFoundations
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Stereographic.FixedPointFoundations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Stereographic/FixedPointFoundations.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Logic.FixedPointFoundations

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 11
-/

noncomputable section

/-- The pre-fixed points of a monotone function: the set of x with f(x) ≤ x.
The least fixed point will bootstrap itself into existence as the infimum
of this set. -/
def preFixedPoints {α : Type*} [Preorder α] (f : α → α) : Set α :=
  {x | f x ≤ x}

/-- The post-fixed points: x ≤ f(x). Dual to pre-fixed points. -/
def postFixedPoints {α : Type*} [Preorder α] (f : α → α) : Set α :=
  {x | x ≤ f x}






/-- A contraction on a metric space: d(f(x), f(y)) ≤ c · d(x, y) for c < 1 -/
def IsContraction {α : Type*} [PseudoMetricSpace α] (f : α → α) (c : ℝ) : Prop :=
  0 ≤ c ∧ c < 1 ∧ ∀ x y : α, dist (f x) (f y) ≤ c * dist x y


/-- Curry's fixed-point combinator, typed in Lean: for any f, we can find x with f x = x
in a complete lattice. This wraps Knaster-Tarski as a function. -/
noncomputable def fixedPointCombinator {α : Type*} [CompleteLattice α]
    (f : α → α) (_hf : Monotone f) : α :=
  sInf (preFixedPoints f)


end


