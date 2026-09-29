-- Prove2me | Theorems.Thm_Zeta23_Poisson_gInt_eq_zero_of_not_mem
-- name    : Zeta23.Poisson.gInt_eq_zero_of_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:57:47.480777+00:00
-- url     : https://prove2.me/theorems/5e574eba-b78a-4d0f-af90-6cf91a214da4
-- title:
--   Support of the Poisson integrand: $g(\xi, u) = 0$ outside $|\xi| < 1$, $|u| < L/2$
-- statement:
--   Fix real parameters $L, T, \tau, \tau'$ and a window $\varphi \colon \mathbb{R} \to \mathbb{R}$, and let
--   $$g(\xi, u) \;=\; L\, \varphi(u)\, \varphi(L\xi - u)\, e^{\,i\,(\tau u + \tau'(L\xi - u) - T L \xi)}$$
--   be the integrand (`gInt`) defining the auxiliary function $G(\xi) = \int g(\xi, u)\, du$. The theorem asserts: if $L > 0$ and $\varphi(u) = 0$ whenever $|u| \ge L/2$, then for any pair $(\xi, u)$ *not* satisfying both $|\xi| < 1$ and $|u| < L/2$,
--   $$g(\xi, u) \;=\; 0.$$
--   Indeed, if $|u| \ge L/2$ the factor $\varphi(u)$ vanishes; and if $|u| < L/2$ but $|\xi| \ge 1$ then $|L\xi - u| \ge L|\xi| - |u| > L/2$, so the factor $\varphi(L\xi - u)$ vanishes.
--
--   This support statement gives $G$ compact support in $[-1,1]$ — in particular $G(k) = 0$ for every nonzero integer $k$, which is why only the $k=0$ term survives on the spatial side of Poisson summation. It is consumed by `Zeta23.Poisson.Gaux_continuous`, `Zeta23.Poisson.fourier_Gaux`, and the core identity `Zeta23.Poisson.hasSum_paperFT_mul_paperFT`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson.lean#L97-L111

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_Taper_Basic

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform
open Zeta23
open Poisson
variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)
variable {φ L T τ τ'}

theorem Zeta23.Poisson.gInt_eq_zero_of_not_mem (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    {ξ u : ℝ} (h : ¬ (|ξ| < 1 ∧ |u| < L / 2)) : gInt φ L T τ τ' ξ u = 0 := by sorry
