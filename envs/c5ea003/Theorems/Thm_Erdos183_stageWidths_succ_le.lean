-- Prove2me | Theorems.Thm_Erdos183_stageWidths_succ_le
-- name    : Erdos183.stageWidths_succ_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:17:30.684397+00:00
-- url     : https://prove2.me/theorems/9f4cda80-3078-4034-b938-952b6290a700
-- title:
--   Stage-to-stage growth of the width parameters
-- statement:
--   For $H \ge 1$, advancing one stage increases the two width parameters by only a controlled amount:
--
--   $$\text{paletteLogWidth}(H+1) \le \text{paletteLogWidth}(H) + 1,$$
--   $$\text{saturatedMatrixWidth}(H+1) \le \text{saturatedMatrixWidth}(H) + 2\,\text{paletteLogWidth}(H) + 4.$$
--
--   These are the discrete Lipschitz estimates that make the parameters vary slowly enough for an arbitrary colour count $k$ to be sandwiched between consecutive stages.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2258-L2325

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.stageWidths_succ_le (H : ℕ) (hH : 1 ≤ H) :
    paletteLogWidth (H + 1) ≤ paletteLogWidth H + 1 ∧
      saturatedMatrixWidth (H + 1) ≤
        saturatedMatrixWidth H + 2 * paletteLogWidth H + 4 := by sorry
