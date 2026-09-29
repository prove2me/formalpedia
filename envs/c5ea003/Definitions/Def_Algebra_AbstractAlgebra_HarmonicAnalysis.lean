-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_HarmonicAnalysis
-- name    : Algebra_AbstractAlgebra_HarmonicAnalysis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:07.517732+00:00
-- url     : https://prove2.me/theorems/2781d309-1324-44ab-8ed6-cfe2df70bb1e
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_HarmonicAnalysis
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.HarmonicAnalysis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/HarmonicAnalysis.lean by skeleton subtraction
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


