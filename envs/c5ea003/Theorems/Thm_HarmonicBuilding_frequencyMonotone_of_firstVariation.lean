-- Prove2me | Theorems.Thm_HarmonicBuilding_frequencyMonotone_of_firstVariation
-- name    : HarmonicBuilding.frequencyMonotone_of_firstVariation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T11:29:52.90401+00:00
-- url     : https://prove2.me/theorems/aaedff5f-ab90-4a0a-a066-2525153c1edb
-- title:
--   Almgren's frequency monotonicity, as a calculus identity
-- statement:
--   Let $E,I,F$ be real functions on an interval $(0,r_0)$ with $I>0$, and suppose
--
--   * $I'(r)=\dfrac{I(r)}{r}+2E(r)$,
--   * $E'(r)\ge 2F(r)$,
--   * $E(r)^2\le I(r)\,F(r)$.
--
--   Then the frequency quotient
--   $$N(r)=\frac{r\,E(r)}{I(r)}$$
--   is monotone nondecreasing on $(0,r_0)$.
--
--   **Role.** This is Almgren's frequency monotonicity, with all of the analysis stripped away. In the application $I(r)$ is the boundary moment of a harmonic map on the circle of radius $r$, $E(r)$ its energy on the disc, and $F(r)$ the boundary integral of the squared radial derivative; the three hypotheses are then, respectively, the elementary derivative of the boundary moment, the domain-variation (first variation) inequality, and the Cauchy--Schwarz inequality relating the energy to the radial derivative. Isolating the computation makes clear that monotonicity of the frequency is not itself an analytic fact: it is a two-line differentiation once those three inputs are available, and it is exactly those inputs that carry the content of the theory.
--
--   **Proof.** Differentiating the quotient,
--   $$N'(r)=\frac{\bigl(E+rE'\bigr)I-rE\Bigl(\frac{I}{r}+2E\Bigr)}{I^{2}}=\frac{r\bigl(E'I-2E^{2}\bigr)}{I^{2}},$$
--   the terms $EI$ cancelling. By the second and third hypotheses $E'I\ge 2FI\ge 2E^{2}$, so the numerator is nonnegative, and $r>0$, $I>0$ give $N'\ge0$ throughout the interval; monotonicity follows from the mean value theorem.
-- source:
--   The computational core of Almgren's frequency monotonicity, as used by M. Gromov and R. Schoen, Harmonic maps into singular spaces and p-adic superrigidity, Publ. Math. IHES 76 (1992), Section 2, and in Section 2 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Mathlib

namespace HarmonicBuilding

theorem frequencyMonotone_of_firstVariation (r₀ : ℝ) (E I F Ederiv : ℝ → ℝ)
    (hI : ∀ r ∈ Set.Ioo (0:ℝ) r₀, 0 < I r)
    (hIderiv : ∀ r ∈ Set.Ioo (0:ℝ) r₀, HasDerivAt I (I r / r + 2 * E r) r)
    (hEderiv : ∀ r ∈ Set.Ioo (0:ℝ) r₀, HasDerivAt E (Ederiv r) r)
    (hEF : ∀ r ∈ Set.Ioo (0:ℝ) r₀, 2 * F r ≤ Ederiv r)
    (hCS : ∀ r ∈ Set.Ioo (0:ℝ) r₀, E r ^ 2 ≤ I r * F r) :
    MonotoneOn (fun r => r * E r / I r) (Set.Ioo 0 r₀) := by sorry

end HarmonicBuilding
