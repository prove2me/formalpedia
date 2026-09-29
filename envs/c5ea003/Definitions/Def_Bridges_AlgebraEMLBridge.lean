-- Prove2me | Definitions.Def_Bridges_AlgebraEMLBridge
-- name    : Bridges_AlgebraEMLBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:54.410476+00:00
-- url     : https://prove2.me/theorems/029350f5-1b83-41bb-8f08-8bbb2444d65e
-- title:
--   Aether Catalog definitions — Bridges_AlgebraEMLBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlgebraEMLBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlgebraEMLBridge.lean by skeleton subtraction
import Mathlib

/-! # Algebra-EML Bridge: Functional Equations

The EML function EML(a,b) = exp(a) - log(b) connects exponential growth
and logarithmic compression.
-/

noncomputable section

namespace AlgebraEMLBridge

def EML (a b : ℝ) : ℝ := Real.exp a - Real.log b







end AlgebraEMLBridge


