-- Prove2me | Theorems.Thm_YukawaPotential_yukawa_total_cross_section
-- name    : YukawaPotential.yukawa_total_cross_section
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T14:36:01.054032+00:00
-- url     : https://prove2.me/theorems/b6abf990-1739-4daf-99b3-e4a3f7df7f73
-- title:
--   Total Born cross section of the Yukawa potential
-- statement:
--   Let $\mu,\hbar,g,p\in\mathbb R$, $\alpha>0$ and $m>0$. Then
--   $$\int_0^\pi \frac{4\mu^2g^4}{\hbar^4}\cdot\frac{2\pi\sin\theta}{\bigl[(\alpha m)^2+4p^2\sin^2(\tfrac12\theta)\bigr]^2}\,d\theta \;=\; \frac{4\mu^2g^4}{\hbar^4}\cdot\frac{4\pi}{(\alpha m)^2\,\bigl[(\alpha m)^2+4p^2\bigr]}.$$
--
--   The integrand is $2\pi\sin\theta$ times the differential cross section $d\sigma/d\Omega=|f(\theta)|^2$ of the Yukawa potential in the Born approximation, so the left side is the total cross section $\sigma=\int\frac{d\sigma}{d\Omega}\,d\Omega$ computed in the section *Cross section*.
--
--   **Formalization Note** The integral is the interval integral over $[0,\pi]$. No sign conditions on $\mu,\hbar,p$ are imposed (the identity is valid for all real values; for $\hbar=0$ both sides are $0$ by Lean's division convention).
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, section 'Cross section': σ = ∫ dσ/dΩ dΩ = (4μ²g⁴/ħ⁴) ∫_0^π 2π sin θ dθ / [(αm)² + 4p² sin²(θ/2)]² = (4μ²g⁴/ħ⁴) · 4π/((αm)²[(αm)² + 4p²]).

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

namespace YukawaPotential
theorem yukawa_total_cross_section (μ ℏ g α m p : ℝ) (hα : 0 < α) (hm : 0 < m) :
    ∫ θ in (0 : ℝ)..Real.pi,
        4 * μ ^ 2 * g ^ 4 / ℏ ^ 4 *
          (2 * Real.pi * Real.sin θ / ((α * m) ^ 2 + 4 * p ^ 2 * Real.sin (θ / 2) ^ 2) ^ 2) =
      4 * μ ^ 2 * g ^ 4 / ℏ ^ 4 * (4 * Real.pi / ((α * m) ^ 2 * ((α * m) ^ 2 + 4 * p ^ 2))) := by sorry
end YukawaPotential
