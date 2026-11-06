-- Prove2me | Theorems.Thm_avram_17372d7a_voidslope_identity_48426407
-- name    : avram_17372d7a_voidslope_identity_48426407
-- status  : Open
-- author  : @WillR
-- created : 2026-11-05T22:40:43.662769+00:00
-- url     : https://prove2.me/theorems/af51c29a-b883-4647-9d4c-491cfb49ad0c
-- title:
--   Avram 17372d7a voidslope: Identity
-- statement:
--   The two expressions in the stated equality coincide under the theorem's explicit assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_nonvoid_second_order_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_occupied_cell_probability
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_bonferroni_void_rate_squeeze_atTop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem avram_17372d7a_voidslope_identity_48426407
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (hT : 0 < T) 
    (hJK : (let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1))); let J : ℝ≥0 → Ω → ℝ≥0∞ := (fun t ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B)); let K : ℝ≥0 → Ω → ℕ := (fun t ω => {u : ℝ≥0 | 0 < u ∧ u ≤ t ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -(1 / ((n : ℝ) + 1))}.ncard); (∀ (t : ℝ≥0) (ω : Ω), J t ω = (K t ω : ℝ≥0∞))))
    (hProb : (let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1))); let J : ℝ≥0 → Ω → ℝ≥0∞ := (fun t ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B)); let K : ℝ≥0 → Ω → ℕ := (fun t ω => {u : ℝ≥0 | 0 < u ∧ u ≤ t ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -(1 / ((n : ℝ) + 1))}.ncard); (∀ (t : ℝ≥0), 1 - (P {ω : Ω | J t ω = 0}).toReal =
        P.real {ω : Ω | K t ω ≠ 0})))
    : (let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1))); let J : ℝ≥0 → Ω → ℝ≥0∞ := (fun t ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B)); let K : ℝ≥0 → Ω → ℕ := (fun t ω => {u : ℝ≥0 | 0 < u ∧ u ≤ t ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -(1 / ((n : ℝ) + 1))}.ncard); let r : ℝ := (T : ℝ) * (X.ν B).toReal; let p : ℕ → ℝ := (fun k => 1 - (P {ω : Ω | J (T / (k : ℝ≥0)) ω = 0}).toReal); Filter.Tendsto (fun k : ℕ => (k : ℝ) * p k)
      Filter.atTop (nhds r)) := by sorry
