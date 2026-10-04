-- Prove2me | Theorems.Thm_YukawaPotential_yukawa_born_amplitude
-- name    : YukawaPotential.yukawa_born_amplitude
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T14:12:04.386023+00:00
-- url     : https://prove2.me/theorems/cac02010-9704-4c2f-bd84-7dd039c40dea
-- title:
--   Born scattering amplitude of the Yukawa potential
-- statement:
--   Let $\mu,\hbar,g\in\mathbb R$, $\alpha>0$, $m>0$, and let $q>0$ denote the momentum transfer $|\vec p-\vec p'|$. With $V(r)=-g^2e^{-\alpha mr}/r$, the first Born approximation
--   $$f = \frac{-2\mu}{\hbar^2 q}\int_0^\infty r\,V(r)\,\sin(qr)\,dr$$
--   evaluates to
--   $$f = \frac{2\mu g^2}{\hbar^2\,[(\alpha m)^2+q^2]}.$$
--
--   This is the step "Evaluating the integral gives" in the section *Cross section*.
--
--   **Formalization Note** The integral is the Lebesgue integral over $(0,\infty)$. No sign conditions on $\mu$ and $\hbar$ are imposed: the identity holds for all real values (for $\hbar=0$ both sides are $0$ by Lean's division convention). The case $q=0$ (forward scattering) is excluded because the article's formula divides by $|\vec p-\vec p'|$.
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, section 'Cross section': f(θ) = -2μ/(ħ²|p-p'|) ∫_0^∞ r V(r) sin(|p-p'| r) dr; plugging in V_Yukawa and evaluating gives f(θ) = 2μg²/(ħ²[(αm)² + |p-p'|²]).

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

namespace YukawaPotential
theorem yukawa_born_amplitude (μ ℏ g α m q : ℝ) (hα : 0 < α) (hm : 0 < m) (hq : 0 < q) :
    -2 * μ / (ℏ ^ 2 * q) * ∫ r in Set.Ioi (0 : ℝ), r * yukawaPotential g α m r * Real.sin (q * r) =
      2 * μ * g ^ 2 / (ℏ ^ 2 * ((α * m) ^ 2 + q ^ 2)) := by sorry
end YukawaPotential
