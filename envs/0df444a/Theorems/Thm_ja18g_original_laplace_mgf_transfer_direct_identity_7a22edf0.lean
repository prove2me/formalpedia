-- Prove2me | Theorems.Thm_ja18g_original_laplace_mgf_transfer_direct_identity_7a22edf0
-- name    : ja18g_original_laplace_mgf_transfer_direct_identity_7a22edf0
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T07:50:28.854772+00:00
-- url     : https://prove2.me/theorems/8147f447-d845-4d5b-a2d2-6ad775cbdcd2
-- title:
--   Ja18g original laplace mgf transfer direct: Identity
-- statement:
--   The two expressions in the stated equality coincide under the theorem's explicit assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem ja18g_original_laplace_mgf_transfer_direct_identity_7a22edf0
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
    (hySmall : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; ∀ᶠ θ in l, |y θ| ≤ 1))
    (hRemBound : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; ∀ᶠ θ in l,
      |(Real.exp (y θ) - 1 - y θ) / θ| ≤ θ * (g θ) ^ 2))
    (hBound0 : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; Tendsto (fun θ => θ * (g θ) ^ 2) l (nhds 0)))
    : (let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0); let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ; let g : ℝ → ℝ := fun θ => y θ / θ; Tendsto
      (fun θ => (Real.exp (y θ) - 1 - y θ) / θ) l (nhds 0)) := by sorry
end
