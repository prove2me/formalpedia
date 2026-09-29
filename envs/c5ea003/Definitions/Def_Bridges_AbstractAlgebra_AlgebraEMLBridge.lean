-- Prove2me | Definitions.Def_Bridges_AbstractAlgebra_AlgebraEMLBridge
-- name    : Bridges_AbstractAlgebra_AlgebraEMLBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:37.641399+00:00
-- url     : https://prove2.me/theorems/90589495-96ca-488c-8f96-5ea997e09a37
-- title:
--   Aether Catalog definitions — Bridges_AbstractAlgebra_AlgebraEMLBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AbstractAlgebra.AlgebraEMLBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AbstractAlgebra/AlgebraEMLBridge.lean by skeleton subtraction
import Mathlib

/-! # Algebra-EML Bridge: Functional Equations

The EML function EML(a,b) = exp(a) - log(b) connects exponential growth
and logarithmic compression.
-/

noncomputable section

namespace AlgebraEMLBridge

def EML (a b : ℝ) : ℝ := Real.exp a - Real.log b







end AlgebraEMLBridge


