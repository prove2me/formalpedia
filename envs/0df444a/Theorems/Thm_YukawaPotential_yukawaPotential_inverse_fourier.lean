-- Prove2me | Theorems.Thm_YukawaPotential_yukawaPotential_inverse_fourier
-- name    : YukawaPotential.yukawaPotential_inverse_fourier
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-03T13:41:57.648975+00:00
-- url     : https://prove2.me/theorems/fa5c0f4b-ed63-4691-a792-58c5e8c29b3a
-- title:
--   Yukawa potential as the inverse Fourier transform of $-g^2\,4\pi/(k^2+(\alpha m)^2)$
-- statement:
--   Let $g\in\mathbb R$, $\alpha>0$, $m>0$, and let $x\in\mathbb R^3$, $x\neq0$. Then
--   $$V(|x|) = \lim_{\Lambda\to\infty}\;\frac{-g^2}{(2\pi)^3}\int_{|k|<\Lambda} e^{i k\cdot x}\,\frac{4\pi}{|k|^2+(\alpha m)^2}\,d^3k,$$
--   where $V(r)=-g^2e^{-\alpha m r}/r$ and $k\cdot x$ is the Euclidean inner product.
--
--   This is the formula of the section *Fourier transform*, with the integral over all momenta $k\in\mathbb R^3$ understood as the limit of integrals over balls.
--
--   **Formalization Note** The function $4\pi/(|k|^2+(\alpha m)^2)$ is not Lebesgue-integrable on $\mathbb R^3$, so the integral over all of $\mathbb R^3$ would be assigned the junk value $0$ in Lean; the statement therefore takes the limit of the integrals over the open balls of radius $\Lambda$ as $\Lambda\to\infty$, computed in $\mathbb C$.
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, section 'Fourier transform': V(r) = (-g²/(2π)³) ∫ e^{ik·r} 4π/(k² + (αm)²) d³k.

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

namespace YukawaPotential
theorem yukawaPotential_inverse_fourier (g α m : ℝ) (hα : 0 < α) (hm : 0 < m)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    Tendsto (fun Λ : ℝ => ((-g ^ 2 / (2 * Real.pi) ^ 3 : ℝ) : ℂ) *
        ∫ k in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) Λ,
          Complex.exp (Complex.I * (inner ℝ k x : ℝ)) *
            ((4 * Real.pi / (‖k‖ ^ 2 + (α * m) ^ 2) : ℝ) : ℂ))
      atTop (𝓝 ((yukawaPotential g α m ‖x‖ : ℝ) : ℂ)) := by sorry
end YukawaPotential
