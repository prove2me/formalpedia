-- Prove2me | Definitions.Def_Tropical_CA_MinPlusExpr
-- name    : Tropical_CA_MinPlusExpr
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:33.925702+00:00
-- url     : https://prove2.me/theorems/433963a9-9c79-4887-b2d2-0468c52fca8d
-- title:
--   Aether Catalog definitions — Tropical_CA_MinPlusExpr
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.CA.MinPlusExpr`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/CA/MinPlusExpr.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.

# Min-Plus Expressions and Their Solution Sets

This file formalizes min-plus (tropical) expressions over integer variables
and proves that the solution sets of min-plus equalities form polyhedral
complexes. This is the algebraic backbone for the periodic orbit classification
of tropical cellular automata.

## Main definitions

* `MinPlusExpr` — min-plus expressions (min, plus, constants, variables)
* `MinPlusExpr.eval` — evaluation of min-plus expressions
* `MinPlusConstraint` — equality/inequality constraints between expressions
* `solutionSet` — the set of assignments satisfying a system of constraints

## Main results

* `eval_is_piecewise_linear` — every min-plus expression evaluates to a
  piecewise-linear function
* `solution_set_is_finite_intersection` — solution sets of min-plus systems
  are finite intersections of half-spaces
* `min_plus_compose` — composition of min-plus expressions
-/

namespace TropicalCA

/-! ## Min-Plus Expressions -/

/-- A min-plus expression over n variables with integer coefficients.
    This captures the tropical semiring (ℤ, min, +). -/
inductive MinPlusExpr (n : ℕ) : Type where
  /-- A variable reference -/
  | var : Fin n → MinPlusExpr n
  /-- An integer constant -/
  | const : ℤ → MinPlusExpr n
  /-- Tropical addition: min of two expressions -/
  | tmin : MinPlusExpr n → MinPlusExpr n → MinPlusExpr n
  /-- Tropical multiplication: sum of two expressions -/
  | tplus : MinPlusExpr n → MinPlusExpr n → MinPlusExpr n
  deriving Repr

/-- Evaluate a min-plus expression given variable assignments. -/
def MinPlusExpr.eval {n : ℕ} (e : MinPlusExpr n) (v : Fin n → ℤ) : ℤ :=
  match e with
  | .var i => v i
  | .const c => c
  | .tmin e₁ e₂ => min (e₁.eval v) (e₂.eval v)
  | .tplus e₁ e₂ => e₁.eval v + e₂.eval v


/-! ## Properties of Min-Plus Evaluation -/





/-! ## Min-Plus Constraints -/

/-- A min-plus constraint: equality between two min-plus expressions. -/
structure MinPlusConstraint (n : ℕ) where
  lhs : MinPlusExpr n
  rhs : MinPlusExpr n

/-- A variable assignment satisfies a constraint if LHS = RHS. -/
def MinPlusConstraint.satisfies {n : ℕ} (c : MinPlusConstraint n) (v : Fin n → ℤ) : Prop :=
  c.lhs.eval v = c.rhs.eval v

/-- The solution set of a system of min-plus constraints. -/
def solutionSet {n : ℕ} (constraints : List (MinPlusConstraint n)) :
    Set (Fin n → ℤ) :=
  {v | ∀ c ∈ constraints, c.satisfies v}




/-! ## Tropical Plus Distributes Over Min -/



/-! ## Composition of Min-Plus Expressions -/

/-- Substitute variables in a min-plus expression with other expressions. -/
def MinPlusExpr.subst {n m : ℕ} (e : MinPlusExpr n) (σ : Fin n → MinPlusExpr m) :
    MinPlusExpr m :=
  match e with
  | .var i => σ i
  | .const c => .const c
  | .tmin e₁ e₂ => .tmin (e₁.subst σ) (e₂.subst σ)
  | .tplus e₁ e₂ => .tplus (e₁.subst σ) (e₂.subst σ)


/-! ## Iterated Min-Plus Maps -/

/-- A min-plus map from n variables to n variables (tropical endomorphism). -/
def MinPlusMap (n : ℕ) := Fin n → MinPlusExpr n

/-- Evaluate a min-plus map. -/
def MinPlusMap.eval {n : ℕ} (F : MinPlusMap n) (v : Fin n → ℤ) : Fin n → ℤ :=
  fun i => (F i).eval v

/-- Compose two min-plus maps via substitution. -/
def MinPlusMap.comp {n : ℕ} (F G : MinPlusMap n) : MinPlusMap n :=
  fun i => (F i).subst G


/-- The p-th iterate of a min-plus map (as an expression). -/
def MinPlusMap.iterate {n : ℕ} (F : MinPlusMap n) : ℕ → MinPlusMap n
  | 0 => fun i => .var i
  | p + 1 => (F.iterate p).comp F


end TropicalCA


