-- Prove2me | Theorems.Thm_avram_chat24_uniform_cell_moments_core
-- name    : avram_chat24_uniform_cell_moments_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:02:51.025752+00:00
-- url     : https://prove2.me/theorems/8c413248-7dab-4b4d-9d33-e534344af959
-- title:
--   avram_chat24_uniform_cell_moments_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_uniform_cell_moments_core from oversized parent candidate 23595c476759eba9b7fdd6476c4a3aa224484b9b77d504c5143dfc6275ebde11.
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
theorem avram_chat24_uniform_cell_moments_core
    (f : ℝ≥0 → ℝ) (d T : ℝ) (hT : 0 ≤ T)
    (B : ℝ≥0) (hB : 0 < B) (hBT : B ≤ (⟨T, hT⟩ : ℝ≥0))
    (hright : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hleft : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hdown : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t)
    (hsum : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' r : ℝ≥0, if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ f t - Function.leftLim f t ≠ 0}).map
        (fun t : ℝ≥0 => (t, f t - Function.leftLim f t)))
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    let m : ℕ → ℕ → ℝ := fun n i =>
      d * h n - (f (u n (i + 1)) - f (u n i))
    ∀ n : ℕ, 0 < h n ∧
      (∀ i ∈ Finset.range (n + 1),
        let H : ℝ≥0 × ℝ → ℝ := fun p =>
          if u n i < p.1 ∧ p.1 ≤ u n (i + 1) then -p.2 else 0
        Integrable H NX ∧ (∫ p, H p ∂NX) = m n i) ∧
      (∀ i ∈ Finset.range (n + 1),
        μ (Ioc (u n i) (u n (i + 1))) = ENNReal.ofReal (h n)) := by sorry
end
