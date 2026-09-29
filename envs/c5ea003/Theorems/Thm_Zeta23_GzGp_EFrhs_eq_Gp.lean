-- Prove2me | Theorems.Thm_Zeta23_GzGp_EFrhs_eq_Gp
-- name    : Zeta23.GzGp.EFrhs_eq_Gp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:45.626972+00:00
-- url     : https://prove2.me/theorems/6c1f7bbf-f902-4d06-b677-bbbe36778f96
-- title:
--   Prime side: the [eq:EF] right-hand side at $(f_k, f_l)$ is the matrix entry $G_{kl}$
-- statement:
--   Fix a parameter pack $P$ (taper profile $\varrho$, exponent $\lambda$, ramp width $w$) and $T$; write $L = \lambda \log(T/2\pi)$, $X = e^{L}$, grid points $\tau_k = T + 2\pi k/L$, taper $\varphi(u) = \varrho((L/2 - |u|)/w)$, and test functions $f_k(u) = \varphi(u)\,e^{-i\tau_k u}$ [eq:fk]. Let $h_{f}(\tau) = \int f(u)e^{i\tau u}\,du$ denote the paper Fourier transform and $\nu_X$ the density of [eq:nudef]. Then for all indices $k, l < d = \lfloor LT/2\pi \rfloor$,
--
--   $$\int_{\mathbb{R}} h_{f_k}(\tau)\,\overline{h_{f_l}(\tau)}\,\nu_X(\tau)\,d\tau \;=\; G_{kl},$$
--
--   where $G_{kl} = \int_{\mathbb{R}} \hat\varphi(\tau-\tau_k)\,\hat\varphi(\tau-\tau_l)\,\nu_X(\tau)\,d\tau$ is the second expression of [eq:Gdef] (the entry of the prime-side matrix `P.Gp`, real-valued and viewed in $\mathbb{C}$). No hypotheses are needed: the identity is the shift formula $h_{f_k}(\tau) = \hat\varphi(\tau - \tau_k)$ together with the fact that $\hat\varphi$ is real on the real axis.
--
--   **Role.** Together with the zero-side identification $G^{z}_{kl} = W(f_k, f_l)$, this shows that hypothesis H-EF applied to the pair $(f_k, f_l)$ yields the equality of the two expressions of [eq:Gdef]; it is consumed by `Zeta23.ZeroConfig.Gz_eq_Gp`, the bridge between the zero-side and prime-side matrices.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Hypotheses/GzGp.lean#L106-L118, docstring tags [eq:EF], [eq:Gdef]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

open scoped ComplexConjugate
open Complex MeasureTheory Set
open Zeta23
variable (P : Params) (T : ℝ)

theorem Zeta23.GzGp.EFrhs_eq_Gp (k l : Fin (P.d T)) :
    (∫ τ : ℝ, paperFT (P.fk T k) τ * conj (paperFT (P.fk T l) τ) *
      (nuX (Real.exp (P.L T)) τ : ℂ)) = P.Gp T k l := by sorry
