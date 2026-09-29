-- Prove2me | Definitions.Def_Logic_AbstractAlgebra_HarmonicAnalysis
-- name    : Logic_AbstractAlgebra_HarmonicAnalysis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:24:29.588524+00:00
-- url     : https://prove2.me/theorems/d2c19636-84ea-4f92-9451-aefce3aa95a3
-- title:
--   Aether Catalog definitions — Logic_AbstractAlgebra_HarmonicAnalysis
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.AbstractAlgebra.HarmonicAnalysis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/AbstractAlgebra/HarmonicAnalysis.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Algebra.HarmonicAnalysis

Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 5
-/


noncomputable section

/-- [Section: # CatalogBuild.Algebra.HarmonicAnalysis
Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 5] -/
noncomputable def discreteConv' (n : ℕ) [NeZero n] (f g : ZMod n → ℂ) : ZMod n → ℂ :=
  fun x => ∑ y : ZMod n, f y * g (x - y)




















end


