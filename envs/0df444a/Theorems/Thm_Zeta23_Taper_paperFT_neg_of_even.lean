-- Prove2me | Theorems.Thm_Zeta23_Taper_paperFT_neg_of_even
-- name    : Zeta23.Taper.paperFT_neg_of_even
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:33:04.441353+00:00
-- url     : https://prove2.me/theorems/e11577af-370b-4314-b1b6-94ae3873eeee
-- title:
--   Evenness of the transform: $h_v(-z) = h_v(z)$ for even $v$
-- statement:
--   For $v : \mathbb{R} \to \mathbb{R}$, let $h_v(z) := \int_{\mathbb{R}} v(u)\,e^{izu}\,du$ be the paper Fourier transform of the complexification of $v$, defined for every complex argument $z$.
--
--   The theorem asserts: if $v$ is even, $v(-u) = v(u)$ for all $u$, then $h_v$ is even on all of $\mathbb{C}$:
--   $$h_v(-z) \;=\; h_v(z) \qquad \text{for every } z \in \mathbb{C},$$
--   by the substitution $u \mapsto -u$ in the defining integral.
--
--   In the project this symmetry lets zero sums and integrals over the taper transforms be folded onto one half-line/half-plane: it is consumed by `Zeta23.PrimeSide.localHyps_concrete`, `Zeta23.Taper.hasSum_phiHatR_mul`, `Zeta23.Taper.integral_PhiR_sq_mul_cos` and `Zeta23.Taper.integral_phiHatR_sq_mul_cos`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Fourier.lean#L65-L74

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

theorem Zeta23.Taper.paperFT_neg_of_even (hv : ∀ u, v (-u) = v u) (z : ℂ) :
    paperFT (fun u => (v u : ℂ)) (-z) = paperFT (fun u => (v u : ℂ)) z := by sorry
