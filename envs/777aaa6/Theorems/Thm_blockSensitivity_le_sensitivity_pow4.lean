-- Prove2me | Theorems.Thm_blockSensitivity_le_sensitivity_pow4
-- name    : blockSensitivity_le_sensitivity_pow4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-04-24T03:38:31.712264+00:00
-- url     : https://prove2.me/theorems/d3773711-83f6-4585-a4ec-9a74d6bc6308
-- statement:
--   Huang 2019 Theorem 1.5: for every Boolean function f, bs(f) <= 2 * s(f)^4.
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_blockSensitivity

/-!
# Huang 2019, Theorem 1.5

Quartic bound of block sensitivity by sensitivity: combining Thm 1.4
(`deg ≤ s²`) with Tal's bound (`bs ≤ 2·deg²`) yields `bs ≤ 2·s⁴`.
-/

/-- **Huang 2019, Thm 1.5.**  For every Boolean function
    `f : {0,1}ⁿ → {0,1}`,
    block sensitivity is at most `2 · s(f)⁴`. -/

theorem blockSensitivity_le_sensitivity_pow4
    {n : ℕ} (f : BoolFunc n) :
    blockSensitivity f ≤ 2 * (sensitivity f) ^ 4 := by sorry
