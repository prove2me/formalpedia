-- Prove2me | Definitions.Def_Speculative_Computation_CompositionAlgebra
-- name    : Speculative_Computation_CompositionAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:32:02.525487+00:00
-- url     : https://prove2.me/theorems/22c3ad95-e9ad-454c-bec5-b2b8d4601510
-- title:
--   Aether Catalog definitions — Speculative_Computation_CompositionAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.Computation.CompositionAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/Computation/CompositionAlgebra.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Computation.CompositionAlgebra

Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 21
-/


noncomputable section

/-- [Section: # CatalogBuild.Computation.CompositionAlgebra
Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 21] -/
def EML_comp (a b : ℝ) : ℝ := Real.exp a - Real.log b




/-- [Section: # CatalogBuild.Computation.CompositionAlgebra
Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 21] -/
def T_op (c : ℝ) (x : ℝ) : ℝ := EML_comp x c




























def L_op (a : ℝ) (y : ℝ) : ℝ := EML_comp a y
























def T_one_iter : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => T_op 1 (T_one_iter n x)




























end


