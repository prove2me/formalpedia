-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_mul_cos_of_paperFT_eq
-- name    : Zeta23.Taper.integral_mul_cos_of_paperFT_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:33:56.085913+00:00
-- url     : https://prove2.me/theorems/5471ea57-946b-44ec-9ccf-e3f8392c7881
-- title:
--   Fourier inversion in cosine form: $h_A = G$ implies $\int G(r)\cos(ry)\,dr = 2\pi A(y)$
-- statement:
--   The paper's Fourier transform of $f : \mathbb{R} \to \mathbb{C}$ is $h_f(z) = \int_{\mathbb{R}} f(u)\,e^{izu}\,du$ (`paperFT`).
--
--   Let $A, G : \mathbb{R} \to \mathbb{R}$ with $A$ continuous and integrable and $G$ integrable, and suppose that $h_A(r) = G(r)$ for every real $r$ (i.e. the transform of $A$, viewed as a complex-valued function, is real and equal to $G$ on the real line). Then for every real $y$,
--
--   $$\int_{\mathbb{R}} G(r)\,\cos(r y)\,dr \;=\; 2\pi\, A(y).$$
--
--   The proof is Fourier inversion $A = \mathcal{F}^{-}\mathcal{F} A$ in Mathlib's normalization, the substitution $r = -2\pi\xi$, and taking real parts; the sine part drops because $A$ is real. This is precisely the form in which the paper invokes \"Fourier inversion\" for $A_\varphi$ ([prop:trace], P-part) and for $g$ ([eq:Phi2FT]); it is consumed by `Zeta23.Taper.integral_phiHatR_sq_mul_cos` and `Zeta23.Taper.integral_PhiR_sq_mul_cos`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Fourier.lean#L217-L268, docstring tags [prop:trace], [eq:Phi2FT]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate
open Zeta23
variable {v : ℝ → ℝ}

theorem Zeta23.Taper.integral_mul_cos_of_paperFT_eq {A G : ℝ → ℝ} (hA : Continuous A) (hAi : Integrable A)
    (hG : Integrable G) (hFT : ∀ r : ℝ, paperFT (fun u => (A u : ℂ)) r = (G r : ℂ)) (y : ℝ) :
    ∫ r, G r * Real.cos (r * y) = 2 * π * A y := by sorry
