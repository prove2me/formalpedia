-- Prove2me | Definitions.Def_Algebra_OISCC_OrbitIteration
-- name    : Algebra_OISCC_OrbitIteration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:26:22.939875+00:00
-- url     : https://prove2.me/theorems/0eb3897b-b3d6-431e-ab29-7faebeb3591a
-- title:
--   Aether Catalog definitions — Algebra_OISCC_OrbitIteration
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.OISCC.OrbitIteration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/OISCC/OrbitIteration.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.OISCC.OrbitIteration

Auto-generated from theorem catalog database.
Domain: Speculative/OISCC
Declarations: 16
-/

noncomputable section

/-- The diagonal map d(x) = exp(x) - ln(x). -/
def d_oi (x : ℝ) : ℝ := Real.exp x - Real.log x

/-- The n-th iterate of the diagonal map. -/
def d_oi_n (n : ℕ) (x : ℝ) : ℝ := d_oi^[n] x















end


