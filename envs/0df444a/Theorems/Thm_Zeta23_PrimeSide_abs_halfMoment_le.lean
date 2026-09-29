-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_halfMoment_le
-- name    : Zeta23.PrimeSide.abs_halfMoment_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:04:23.396493+00:00
-- url     : https://prove2.me/theorems/db096219-d14d-4743-8458-115741216ca3
-- title:
--   Half-line moment bound: $\bigl|\int_a^b \Phi^2 g\bigr| \le \int_{\mathbb{R}} \Phi^2$ for $|g| \le 1$
-- statement:
--   Let $\Phi : \mathbb{R} \to \mathbb{R}$ be continuous with $\Phi^2$ integrable, let $a \le b$ be reals, and let $g : \mathbb{R} \to \mathbb{R}$ be continuous with $|g(x)| \le 1$ for all $x$. Then
--   $$\Bigl|\int_a^b \Phi(x)^2\, g(x)\, dx\Bigr| \;\le\; \int_{\mathbb{R}} \Phi(x)^2\, dx.$$
--   This is the elementary estimate behind the paper's bound $|\alpha_n^{\pm}| \le \pi b L$ on the half-line moments of Section 5.4 (there $g$ is a sine or cosine); the formalization uses the cruder bound by the full integral $\int \Phi^2 = 2\pi b L$, the constants being immaterial.
--
--   In the project it bounds the trigonometric moments $C^{\pm}, S^{\pm}$ appearing in the closed-form evaluation of the off-diagonal kernel $A^-$, and feeds `O1_bound`, the $O(1)$-per-pair off-diagonal estimate in the proof of [prop:PP] (module `Zeta23.PrimeSideB.PPKernel`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L489-L506

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Zeta23
open PrimeSide
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem Zeta23.PrimeSide.abs_halfMoment_le (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) {a b : ℝ}
    (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hg1 : ∀ x, |g x| ≤ 1) :
    |∫ x in a..b, Φ x ^ 2 * g x| ≤ ∫ x, Φ x ^ 2 := by sorry
