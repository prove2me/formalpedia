-- Prove2me | Theorems.Thm_Zeta23_Taper_contDiff_paperFT_ofReal
-- name    : Zeta23.Taper.contDiff_paperFT_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:32:09.493535+00:00
-- url     : https://prove2.me/theorems/6e810c07-336a-46db-8a9d-b93beeb533a2
-- title:
--   Smoothness of $h_f$ on $\mathbb{R}$ for continuous compactly supported $f$
-- statement:
--   The paper's Fourier transform of $f : \mathbb{R} \to \mathbb{C}$ is $h_f(z) = \int_{\mathbb{R}} f(u)\,e^{izu}\,du$ (`paperFT`).
--
--   Suppose $f$ is continuous with compact support. Then for every $n \in \mathbb{N} \cup \{\infty\}$, the restriction of $h_f$ to the real line, $r \mapsto h_f(r)$, is $C^n$ as a function $\mathbb{R} \to \mathbb{C}$; that is, it is smooth.
--
--   The proof passes through the dictionary to Mathlib's Fourier transform $\mathcal{F}$ and `Real.contDiff_fourier`. The lemma supplies the smoothness input for `Zeta23.Taper.integrable_re_paperFT_sq_and` and for `Zeta23.PrimeSide.localHyps_concrete` on the prime side of the explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Fourier.lean#L82-L94

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

theorem Zeta23.Taper.contDiff_paperFT_ofReal {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (n : ℕ∞) : ContDiff ℝ n (fun r : ℝ => paperFT f r) := by sorry
