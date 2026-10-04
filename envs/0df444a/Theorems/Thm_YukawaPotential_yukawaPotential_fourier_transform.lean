-- Prove2me | Theorems.Thm_YukawaPotential_yukawaPotential_fourier_transform
-- name    : YukawaPotential.yukawaPotential_fourier_transform
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-03T13:59:15.129755+00:00
-- url     : https://prove2.me/theorems/0d3b2986-d38e-419a-8b8c-4fba5ed1c3e8
-- title:
--   Fourier transform of the Yukawa potential: $\hat V(k) = -g^2\,4\pi/(|k|^2+(\alpha m)^2)$
-- statement:
--   Let $g\in\mathbb R$, $\alpha>0$ and $m>0$, and let $V(r)=-g^2e^{-\alpha m r}/r$. For every $k\in\mathbb R^3$,
--   $$\int_{\mathbb R^3} e^{-i\,k\cdot x}\,V(|x|)\,d^3x \;=\; -g^2\,\frac{4\pi}{|k|^2+(\alpha m)^2}.$$
--
--   This is the momentum-space form of the Yukawa potential: the sections *Fourier transform* and *Feynman amplitude* identify $-g^2\cdot 4\pi/(k^2+m^2)$ (with $\alpha=1$), the lowest-order single-meson-exchange amplitude, as the Fourier transform of the Yukawa potential, with $4\pi/(k^2+m^2)$ the propagator (Green's function) of the Klein–Gordon equation.
--
--   **Formalization Note** The integral is a Lebesgue (Bochner) integral over `EuclideanSpace ℝ (Fin 3)`, which converges absolutely for $\alpha m>0$; the value of the integrand at the single point $x=0$ is irrelevant. The convention is $\hat V(k)=\int e^{-ik\cdot x}V(|x|)\,d^3x$, matching the inverse formula $V=(2\pi)^{-3}\int e^{ik\cdot x}\hat V\,d^3k$ of the article.
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, sections 'Fourier transform' and 'Feynman amplitude': V(k) = -g² 4π/(k² + m²) 'is seen to be the Fourier transform of the Yukawa potential'.

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

namespace YukawaPotential
theorem yukawaPotential_fourier_transform (g α m : ℝ) (hα : 0 < α) (hm : 0 < m)
    (k : EuclideanSpace ℝ (Fin 3)) :
    ∫ x : EuclideanSpace ℝ (Fin 3),
        Complex.exp (-(Complex.I * (inner ℝ k x : ℝ))) * ((yukawaPotential g α m ‖x‖ : ℝ) : ℂ) =
      ((-g ^ 2 * (4 * Real.pi / (‖k‖ ^ 2 + (α * m) ^ 2)) : ℝ) : ℂ) := by sorry
end YukawaPotential
