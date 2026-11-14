-- Prove2me | Theorems.Thm_avram_chat24_physical_cell_volume_core
-- name    : avram_chat24_physical_cell_volume_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:02:48.295501+00:00
-- url     : https://prove2.me/theorems/252e096b-2036-48d2-9617-33bd9da14e24
-- title:
--   avram_chat24_physical_cell_volume_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_physical_cell_volume_core from oversized parent candidate 23595c476759eba9b7fdd6476c4a3aa224484b9b77d504c5143dfc6275ebde11.
-- source:
--   candidate-decomposition:ceff8522-80f3-4b18-bd1f-7f8919134883:23595c476759eba9b7fdd6476c4a3aa224484b9b77d504c5143dfc6275ebde11

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem avram_chat24_physical_cell_volume_core (T : ℝ) (s t : ℝ≥0)
    (hst : s ≤ t) (htT : (t : ℝ) ≤ T) :
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    μ (Ioc s t) = ENNReal.ofReal ((t : ℝ) - (s : ℝ)) := by sorry
end
