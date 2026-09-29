-- Prove2me | Definitions.Def_Speculative_OISCC_DiagonalMap
-- name    : Speculative_OISCC_DiagonalMap
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:28.89278+00:00
-- url     : https://prove2.me/theorems/7cd71be0-1025-4121-8be6-e7bf76511aca
-- title:
--   Aether Catalog definitions — Speculative_OISCC_DiagonalMap
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.OISCC.DiagonalMap`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/OISCC/DiagonalMap.lean by skeleton subtraction
import Mathlib
/-
# OISCC V9.1: The Diagonal Map d(x) = exp(x) - ln(x)
-/


noncomputable section

open Real Filter Topology Set

/-- The diagonal map d(x) = exp(x) - ln(x). -/
def diagMap (x : ℝ) : ℝ := Real.exp x - Real.log x








/-- Iterated diagonal map. -/
def diagIter : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => diagMap (diagIter n x)

/-
diagIter (n+1) x > diagIter n x for x > 0.
-/

/-
d is strictly convex on (0, ∞).
-/

end


