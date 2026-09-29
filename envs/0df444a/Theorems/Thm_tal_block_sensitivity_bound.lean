-- Prove2me | Theorems.Thm_tal_block_sensitivity_bound
-- name    : tal_block_sensitivity_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-04-24T03:38:15.821461+00:00
-- url     : https://prove2.me/theorems/86321603-4d06-4be0-9460-355a1de9a094
-- statement:
--   Tal 2013 (improving Nisan-Szegedy 1994): for every Boolean function f, block sensitivity is at most 2 times the polynomial degree squared, bs(f) <= 2 * deg(f)^2.
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Definitions.Def_BoolFunc
import Definitions.Def_blockSensitivity
import Definitions.Def_polyDegree

/-!
# Tal 2013 / Nisan–Szegedy block-sensitivity ⇔ degree bound

The quadratic bound `bs(f) ≤ 2 · deg(f)²` used by Huang 2019 to convert
the sensitivity/degree bound of Thm 1.4 into the sensitivity/block-
sensitivity bound of Thm 1.5.

Left as a platform leaf (`sorry`) — a full proof is outside the scope
of this decomposition pass.
-/

/-- **Tal 2013 (improving Nisan–Szegedy 1994).**  For every Boolean
    function `f : {0,1}ⁿ → {0,1}`,
    block sensitivity is quadratically bounded by polynomial degree:
    `bs(f) ≤ 2 · deg(f)²`. -/

theorem tal_block_sensitivity_bound
    {n : ℕ} (f : BoolFunc n) :
    blockSensitivity f ≤ 2 * (polyDegree f) ^ 2 := by sorry
