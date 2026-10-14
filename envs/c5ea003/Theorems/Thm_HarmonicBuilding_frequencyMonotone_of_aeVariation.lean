-- Prove2me | Theorems.Thm_HarmonicBuilding_frequencyMonotone_of_aeVariation
-- name    : HarmonicBuilding.frequencyMonotone_of_aeVariation
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T10:54:08.138895+00:00
-- url     : https://prove2.me/theorems/905b46b1-832b-4e70-8a70-7431b598f3b2
-- title:
--   Frequency monotonicity from almost-everywhere weak variation
-- statement:
--   Let $R$ be real, and let $E,I,J,F$ be real-valued functions of the radius. Suppose $I>0$ and $E\geq0$ on $(0,R)$, and $E,I$ are absolutely continuous on every compact subinterval. Assume, for almost every $r\in(0,R)$,
--   $$
--   I'(r)=\frac{I(r)}r+2J(r),\qquad E'(r)=2F(r),\qquad
--   E(r)\leq J(r),\qquad J(r)^2\leq I(r)F(r).
--   $$
--   Then
--   $$
--   r\longmapsto\frac{rE(r)}{I(r)}
--   $$
--   is nondecreasing on $(0,R)$.
--
--   This isolates the real-analysis part of the two-dimensional frequency formula. The function $J$ represents half the boundary radial flux; equality of flux and energy is not required. For $R\leq0$ the conclusion is vacuous.
-- source:
--   Gromov and Schoen, Harmonic maps into singular spaces and p-adic superrigidity for lattices in groups of rank one, IHES Publ. Math. 76 (1992), Section 2, Proposition 2.2 and equations (2.2)-(2.5), printed pp. 191-194: https://www.ihes.fr/~gromov/wp-content/uploads/2018/08/785.pdf. The calculus statement below is the two-dimensional scalar consequence, with the radial flux retained as a separate function.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

open Set MeasureTheory Filter
open scoped Topology intervalIntegral
set_option autoImplicit false

theorem HarmonicBuilding.frequencyMonotone_of_aeVariation (R : ℝ) (E I J F : ℝ → ℝ)
    (hI : ∀ r ∈ Ioo (0 : ℝ) R, 0 < I r)
    (hE : ∀ r ∈ Ioo (0 : ℝ) R, 0 ≤ E r)
    (hAC : ∀ a b : ℝ, 0 < a → a ≤ b → b < R →
      AbsolutelyContinuousOnInterval E a b ∧ AbsolutelyContinuousOnInterval I a b)
    (hvar : ∀ᵐ r : ℝ, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt I (I r / r + 2 * J r) r ∧
      HasDerivAt E (2 * F r) r ∧ E r ≤ J r ∧ J r ^ 2 ≤ I r * F r) :
    MonotoneOn (fun r => r * E r / I r) (Ioo (0 : ℝ) R) := by sorry
