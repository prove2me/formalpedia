-- Prove2me | Theorems.Thm_avram_chat24_count_nonneg_tsum_core
-- name    : avram_chat24_count_nonneg_tsum_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:03:07.211921+00:00
-- url     : https://prove2.me/theorems/eceabf3b-3575-4de9-8298-2f75f056ce10
-- title:
--   avram_chat24_count_nonneg_tsum_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_count_nonneg_tsum_core from oversized parent candidate 23595c476759eba9b7fdd6476c4a3aa224484b9b77d504c5143dfc6275ebde11.
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
theorem avram_chat24_count_nonneg_tsum_core
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (g : α → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hg : Summable g) :
    Integrable g Measure.count ∧ (∫ x, g x ∂Measure.count) = ∑' x, g x := by sorry
end
