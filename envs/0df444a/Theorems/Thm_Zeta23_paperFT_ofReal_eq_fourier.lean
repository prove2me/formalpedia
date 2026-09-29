-- Prove2me | Theorems.Thm_Zeta23_paperFT_ofReal_eq_fourier
-- name    : Zeta23.paperFT_ofReal_eq_fourier
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:31:53.186652+00:00
-- url     : https://prove2.me/theorems/c07a20f8-870d-4f79-8b3d-8e28f74f0676
-- title:
--   Convention dictionary: $h_f(s) = \mathcal{F}f\big({-s}/{2\pi}\big)$ for real $s$
-- statement:
--   The project states all paper-side results in the paper's Fourier convention `paperFT`, $h_f(z) = \int_{\mathbb{R}} f(u)\, e^{izu}\, du$, while Mathlib's Fourier transform is $\mathcal{F}f(w) = \int_{\mathbb{R}} f(v)\, e^{-2\pi i v w}\, dv$. This lemma is the dictionary between the two on the real line: for every $f : \mathbb{R} \to \mathbb{C}$ and every **real** argument $s$,
--   $$h_f(s) \;=\; \mathcal{F} f\Big(\frac{-s}{2\pi}\Big).$$
--   No integrability hypothesis is needed — both sides are the same integral after the linear change of phase, and Lean's convention gives both sides the junk value $0$ when the integral does not exist.
--
--   The dictionary lets the project import Mathlib's Fourier analysis (smoothness of transforms, Plancherel-type inputs, Poisson summation) into paper-convention statements. From `Zeta23.Poisson.PaperFT` it is consumed by `Zeta23.Taper.contDiff_paperFT_ofReal`, `Zeta23.Taper.integral_mul_cos_of_paperFT_eq`, and `Zeta23.Taper.paperFT_autocorr`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson/PaperFT.lean#L40-L51

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23

theorem Zeta23.paperFT_ofReal_eq_fourier (f : ℝ → ℂ) (s : ℝ) :
    paperFT f s = 𝓕 f (-s / (2 * π)) := by sorry
