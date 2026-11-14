-- Prove2me | Theorems.Thm_avram_chat24_atomic_prefix_interval_core
-- name    : avram_chat24_atomic_prefix_interval_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:02:48.037076+00:00
-- url     : https://prove2.me/theorems/1514304d-ef4b-4631-8a3a-0c152e50d910
-- title:
--   avram_chat24_atomic_prefix_interval_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_atomic_prefix_interval_core from oversized parent candidate 23595c476759eba9b7fdd6476c4a3aa224484b9b77d504c5143dfc6275ebde11.
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
theorem avram_chat24_atomic_prefix_interval_core
    (f : ℝ≥0 → ℝ) (d : ℝ) (B : ℝ≥0)
    (hsum : Summable (fun r : ℝ≥0 =>
      if 0 < r ∧ r ≤ B then Function.leftLim f r - f r else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' r : ℝ≥0, if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0)
    (s t : ℝ≥0) (hst : s ≤ t) (htB : t ≤ B) :
    Summable (fun r : ℝ≥0 =>
      if s < r ∧ r ≤ t then Function.leftLim f r - f r else 0) ∧
    (∑' r : ℝ≥0, if s < r ∧ r ≤ t then Function.leftLim f r - f r else 0) =
      ((t : ℝ) - (s : ℝ)) * d - (f t - f s) := by sorry
end
