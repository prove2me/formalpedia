-- Prove2me | Theorems.Thm_ja18g_original_laplace_mgf_transfer_direct_pointwise_upper_bound_b1160982
-- name    : ja18g_original_laplace_mgf_transfer_direct_pointwise_upper_bound_b1160982
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:50:30.844434+00:00
-- url     : https://prove2.me/theorems/6eba36e0-01e1-426f-b637-9ea6e822cc42
-- title:
--   Ja18g original laplace mgf transfer direct: Pointwise upper bound
-- statement:
--   At every point covered by the stated hypotheses, the left-hand expression is at most the right-hand expression.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem ja18g_original_laplace_mgf_transfer_direct_pointwise_upper_bound_b1160982
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (a : ℝ)
    (hψ : Filter.Tendsto (fun θ : ℝ => X.ψ θ / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds a)) 
    (hθ : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; Tendsto (fun θ : ℝ => θ) l (nhds 0)))
    (hg : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; Tendsto g l (nhds ((t : ℝ) * a))))
    (hpos : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; ∀ᶠ θ in l, 0 < θ))
    (hy0 : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; Tendsto y l (nhds 0)))
    : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; ∀ᶠ θ in l, |y θ| ≤ 1) := by sorry
end
