-- Prove2me | Theorems.Thm_avram_chat24_physical_discount_cell_integral_core
-- name    : avram_chat24_physical_discount_cell_integral_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:21:24.407666+00:00
-- url     : https://prove2.me/theorems/68162ee6-d56e-4f89-804c-42c548bcf6f7
-- title:
--   avram_chat24_physical_discount_cell_integral_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_physical_discount_cell_integral_core from oversized parent candidate 62347c3a2857c24662d5edb65fbdee2afae4561fe41c58af30436dabfbc40419.
-- source:
--   candidate-decomposition:966a885e-1f3b-4988-ade7-7c1ab4049f80:62347c3a2857c24662d5edb65fbdee2afae4561fe41c58af30436dabfbc40419

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
theorem avram_chat24_physical_discount_cell_integral_core (q T : ℝ) (hT : 0 ≤ T)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : (t : ℝ) ≤ T) :
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    (∫ r in Ioc s t, Real.exp (-(q * (r : ℝ))) * (-q) ∂μ) =
      Real.exp (-(q * (t : ℝ))) - Real.exp (-(q * (s : ℝ))) := by sorry
end
