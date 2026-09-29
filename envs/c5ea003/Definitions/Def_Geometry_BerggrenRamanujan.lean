-- Prove2me | Definitions.Def_Geometry_BerggrenRamanujan
-- name    : Geometry_BerggrenRamanujan
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:51:45.28452+00:00
-- url     : https://prove2.me/theorems/46b1a66d-68af-40b2-8ed0-3c350584102d
-- title:
--   Aether Catalog definitions — Geometry_BerggrenRamanujan
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.BerggrenRamanujan`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/BerggrenRamanujan.lean by skeleton subtraction
import Mathlib

open Matrix

/-! # CatalogBuild.Pythagorean.Berggren.BerggrenRamanujan

Auto-generated from theorem catalog database.
Domain: Pythagorean/Berggren
Declarations: 59
-/

noncomputable section

/-- A direction in the ternary Berggren tree. -/
inductive BDir where
  | left  : BDir   -- B₁ branch
  | mid   : BDir   -- B₂ branch
  | right : BDir   -- B₃ branch
  deriving DecidableEq, Repr, Inhabited

/-- A position in the Berggren tree is a finite word over {left, mid, right}. -/
abbrev BPos := List BDir

/-- Apply a single Berggren step. -/
def berggrenStep (d : BDir) (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  let (a, b, c) := t
  match d with
  | .left  => (a - 2*b + 2*c, 2*a - b + 2*c, 2*a - 2*b + 3*c)
  | .mid   => (a + 2*b + 2*c, 2*a + b + 2*c, 2*a + 2*b + 3*c)
  | .right => (-a + 2*b + 2*c, -2*a + b + 2*c, -2*a + 2*b + 3*c)

/-- The Pythagorean triple at a given position (path applied left-to-right from root). -/
def berggrenAt (path : BPos) : ℤ × ℤ × ℤ :=
  path.foldl (fun t d => berggrenStep d t) (3, 4, 5)



/-- Berggren matrix B₁. -/
def berggrenB₁ : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -2, 2; 2, -1, 2; 2, -2, 3]

/-- Berggren matrix B₂. -/
def berggrenB₂ : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 2, 2; 2, 1, 2; 2, 2, 3]

/-- Berggren matrix B₃. -/
def berggrenB₃ : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(-1), 2, 2; (-2), 1, 2; (-2), 2, 3]







/-- The Lorentz form matrix: diag(1, 1, -1). -/
def berggren_Q : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, (-1)]









/-- The Ramanujan bound for a d-regular graph: 2√(d-1). -/
noncomputable def ramanujanBound (d : ℕ) : ℝ := 2 * Real.sqrt (d - 1 : ℝ)





/-- The spectral gap of a 3-regular Ramanujan graph: d - λ₂ = 3 - 2√2. -/
noncomputable def spectralGap3 : ℝ := 3 - 2 * Real.sqrt 2

/-- The spectral gap of a 4-regular Ramanujan graph: 4 - 2√3. -/
noncomputable def spectralGap4 : ℝ := 4 - 2 * Real.sqrt 3



/-- The Berggren tree adjacency relation: two positions are adjacent
if one extends the other by exactly one step. -/
def berggrenAdj (p q : BPos) : Prop :=
  (∃ d : BDir, q = p ++ [d]) ∨ (∃ d : BDir, p = q ++ [d])


















/-- The Cheeger constant lower bound for a d-regular graph with spectral gap γ:
h(G) ≥ γ/2 (Cheeger inequality, easy direction). -/
noncomputable def cheegerBound3 : ℝ := spectralGap3 / 2








end


