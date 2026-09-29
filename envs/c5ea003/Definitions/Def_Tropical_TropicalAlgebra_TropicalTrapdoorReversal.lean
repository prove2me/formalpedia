-- Prove2me | Definitions.Def_Tropical_TropicalAlgebra_TropicalTrapdoorReversal
-- name    : Tropical_TropicalAlgebra_TropicalTrapdoorReversal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:12.967195+00:00
-- url     : https://prove2.me/theorems/41ebd1d9-d41c-4fc5-b483-dbf7db607eec
-- title:
--   Aether Catalog definitions — Tropical_TropicalAlgebra_TropicalTrapdoorReversal
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.TropicalAlgebra.TropicalTrapdoorReversal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/TropicalAlgebra/TropicalTrapdoorReversal.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Tropical.Cryptography.TropicalTrapdoorReversal

Auto-generated from theorem catalog database.
Domain: Tropical/Cryptography
Declarations: 29
-/

noncomputable section





/-- A tropical half-space constraint -/
inductive TropConstraint where
  | LeShift (i j : ℕ) (c : ℝ) : TropConstraint  -- x_i ≤ x_j + c
  | EqSum (i j : ℕ) (c : ℝ) : TropConstraint     -- x_i + x_j = c
  | EqConst (i : ℕ) (c : ℝ) : TropConstraint      -- x_i = c

/-- Satisfaction of a tropical constraint -/
def satisfiesConstraint (x : ℕ → ℝ) : TropConstraint → Prop
  | .LeShift i j c => x i ≤ x j + c
  | .EqSum i j c => x i + x j = c
  | .EqConst i c => x i = c

/-- A tropical polyhedron is defined by a list of constraints -/
abbrev TropPolyhedron := List TropConstraint

/-- The feasible set of a tropical polyhedron -/
def feasibleSet (poly : TropPolyhedron) : Set (ℕ → ℝ) :=
  {x | ∀ c ∈ poly, satisfiesConstraint x c}



/-- A linearized gate: after fixing selections, each gate is either
"take left", "take right", or "add" -/
inductive LinearizedGate where
  | TakeLeft : LinearizedGate
  | TakeRight : LinearizedGate
  | Add : LinearizedGate

/-- Evaluate a linearized gate -/
def evalLinearized (lg : LinearizedGate) (a b : ℝ) : ℝ :=
  match lg with
  | .TakeLeft => a
  | .TakeRight => b
  | .Add => a + b






/-- A min-gate selection is consistent if the selected value is indeed the minimum -/
def minSelectionConsistent (a b : ℝ) (selectLeft : Bool) : Prop :=
  if selectLeft then a ≤ b else b ≤ a

/-- A max-gate selection is consistent if the selected value is indeed the maximum -/
def maxSelectionConsistent (a b : ℝ) (selectLeft : Bool) : Prop :=
  if selectLeft then b ≤ a else a ≤ b











end


