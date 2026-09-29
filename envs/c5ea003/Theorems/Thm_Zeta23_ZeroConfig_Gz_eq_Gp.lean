-- Prove2me | Theorems.Thm_Zeta23_ZeroConfig_Gz_eq_Gp
-- name    : Zeta23.ZeroConfig.Gz_eq_Gp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:53:38.690173+00:00
-- url     : https://prove2.me/theorems/4d8d82c3-4afe-4cf2-b9d2-4b9835e6e361
-- title:
--   The H-EF bridge: zero-side and prime-side matrices agree
-- statement:
--   Let $Z$ be an abstract zero configuration, $P$ a choice of fixed parameters (taper profile $\varrho$, exponent $\lambda$ with $X = (T/2\pi)^\lambda$, ramp width $w$), and $T$ a height. With $L = \lambda \log(T/2\pi)$, taper $\varphi(u) = \varrho((L/2 - |u|)/w)$, grid points $\tau_k = T + 2\pi k/L$ and $d = \lfloor LT/2\pi \rfloor$, the paper's matrix $G$ [eq:Gdef] has two expressions:
--   - the **zero side** $G^{\mathrm z}_{kl} = \sum_\rho m_\rho\, \hat\varphi(\gamma_\rho - \tau_k)\, \hat\varphi(\gamma_\rho - \tau_l)$ (a `tsum` over all distinct zeros of $Z$; `Z.Gz P T`), and
--   - the **prime side** $G^{\mathrm p}_{kl} = \int_{\mathbb{R}} \hat\varphi(\tau - \tau_k)\, \hat\varphi(\tau - \tau_l)\, \nu_X(\tau)\, d\tau$ with $X = e^L$ (`P.Gp T`).
--
--   **Statement.** Assume H-EF (`ExplicitFormulaPaper Z`: the paper-form Weil explicit formula $W(f, g) = \int h_f \overline{h_g}\, \nu_X$ for all $C^2$ test functions supported in $[-L/2, L/2]$, together with its summability and integrability clauses), that $L(T) > 0$, that $\varphi \in C^2$ (as a complex-valued function), and that $\operatorname{supp} \varphi \subseteq [-L/2, L/2]$. Then
--   $$Z.\mathrm{Gz}\; P\; T \;=\; P.\mathrm{Gp}\; T,$$
--   i.e. the two $d \times d$ matrices are equal entrywise. The proof applies H-EF to the test pair $f_k, f_l$ where $f_k(u) = \varphi(u) e^{-i\tau_k u}$, using $h_{f_k}(z) = \hat\varphi(z - \tau_k)$ and the realness of $\hat\varphi$ on $\mathbb{R}$.
--
--   **Role.** In the module `Zeta23.Hypotheses.GzGp` this bridge lets the matrix-variational argument evaluate the Gram matrix $G$ on the prime side; it is consumed by `Zeta23.eventually_side_conditions` on the way to Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Hypotheses/GzGp.lean#L122-L132, docstring tag [eq:Gdef]

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
import Definitions.Def_Zeta23_Hypotheses

open scoped ComplexConjugate
open Complex MeasureTheory Set
open Zeta23

theorem Zeta23.ZeroConfig.Gz_eq_Gp (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hEF : ExplicitFormulaPaper Z) (hL : 0 < P.L T)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) :
    Z.Gz P T = P.Gp T := by sorry
