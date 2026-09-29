-- Prove2me | Theorems.Thm_Erdos183_two_mul_stage_le_paletteColourCount
-- name    : Erdos183.two_mul_stage_le_paletteColourCount
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:18:09.794477+00:00
-- url     : https://prove2.me/theorems/7f77b421-0164-4801-9e69-0dca10fa1d2a
-- title:
--   The palette colour count grows at least linearly
-- statement:
--   For every $H$,
--
--   $$2H \;\le\; \text{paletteColourCount}(H).$$
--
--   This ensures the stages of the construction exhaust every colour count, so that the sandwiching argument reaches all sufficiently large $k$.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2382-L2395

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Nat

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.two_mul_stage_le_paletteColourCount (H : ℕ) :
    2 * H ≤ paletteColourCount H := by sorry
