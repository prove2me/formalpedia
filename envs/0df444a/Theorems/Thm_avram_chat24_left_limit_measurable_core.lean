-- Prove2me | Theorems.Thm_avram_chat24_left_limit_measurable_core
-- name    : avram_chat24_left_limit_measurable_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:02:52.60809+00:00
-- url     : https://prove2.me/theorems/e48a1e4f-d06c-47e4-abaf-889f3ce118a6
-- title:
--   avram_chat24_left_limit_measurable_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_left_limit_measurable_core from oversized parent candidate 23595c476759eba9b7fdd6476c4a3aa224484b9b77d504c5143dfc6275ebde11.
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
theorem avram_chat24_left_limit_measurable_core (f : ℝ≥0 → ℝ)
    (hf : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l)) :
    Measurable (Function.leftLim f) := by sorry
end
