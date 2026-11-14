-- Prove2me | Theorems.Thm_avram_chat24_mapped_jump_cell_integral_core
-- name    : avram_chat24_mapped_jump_cell_integral_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:02:52.59221+00:00
-- url     : https://prove2.me/theorems/a665abbb-a709-4306-96ad-c88027a3db74
-- title:
--   avram_chat24_mapped_jump_cell_integral_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_mapped_jump_cell_integral_core from oversized parent candidate 23595c476759eba9b7fdd6476c4a3aa224484b9b77d504c5143dfc6275ebde11.
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
theorem avram_chat24_mapped_jump_cell_integral_core
    (Δ : ℝ≥0 → ℝ) (hΔ : Measurable Δ)
    (hdown : ∀ r : ℝ≥0, 0 < r → Δ r ≤ 0)
    (s t : ℝ≥0)
    (hsum : Summable (fun r : ℝ≥0 => if s < r ∧ r ≤ t then -Δ r else 0)) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ Δ r ≠ 0}).map
        (fun r : ℝ≥0 => (r, Δ r)))
    let H : ℝ≥0 × ℝ → ℝ := fun p => if s < p.1 ∧ p.1 ≤ t then -p.2 else 0
    Integrable H NX ∧ (∫ p, H p ∂NX) =
      ∑' r : ℝ≥0, if s < r ∧ r ≤ t then -Δ r else 0 := by sorry
end
