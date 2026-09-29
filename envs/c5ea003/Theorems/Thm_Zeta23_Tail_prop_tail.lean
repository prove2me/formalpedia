-- Prove2me | Theorems.Thm_Zeta23_Tail_prop_tail
-- name    : Zeta23.Tail.prop_tail
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:46:41.742304+00:00
-- url     : https://prove2.me/theorems/617e5793-c3e1-45e2-b5cf-8143034ebc55
-- title:
--   Proposition [prop:tail]: $\|\tilde E\| \le \theta_0$ and $\|\hat E\|_1 \le \theta_0/(aL)$
-- statement:
--   **Setup.** Let $Z$ be a zero configuration and $P$ parameters, and let $E := $ `Z.Ez P T` $= G - A$ be the concrete tail matrix of [eq:AE] — the contribution to the $d\times d$ zero-side matrix of the zeros with ordinate outside $I' = (T - \sqrt T,\, 2T + \sqrt T]$ (including all zeros with $\gamma \le 0$). Its rescalings are $\tilde E := E/L$ (tilde units, `P.tilde`) and $\hat E := E/(aL^2)$ (hat units, `P.hat`), with $L = \lambda\ell(T)$ and $a = L^{-1}\int\varphi^2$. Assume the hypothesis bundle `TailHyp Z P T A₀ C₁`: $T \ge T_0 := 300$, $L \ge 2$, $A_0 \ge 1$ with the unit-window local zero count (from `PaperInputs.RvM.local`), $C_1 \ge 0$, and the decay [eq:hfbound] for $\hat\varphi$ (from `Taper.lean`); additionally $a > 0$ and that $\tilde E$, $\hat E$ are Hermitian (which comes from the $\rho \mapsto 1 - \bar\rho$ symmetry). Write
--   $$\theta_0 \;:=\; \theta_0\!\bigl(A_0,\, e^{L/4}C_1,\, T\bigr) \;=\; \frac{4A_0\,(e^{L/4}C_1)^2 \log(4T)}{T} \;=\; \frac{4A_0\,C_1^2\, X^{1/2}\log(4T)}{D_0^{2}},$$
--   and recall `traceNorm` of a Hermitian matrix is $\sum_i|\lambda_i|$.
--
--   **Statement.** All three of:
--   $$\text{(T1)}\ \ |\lambda_i(\tilde E)| \le \theta_0 \ \text{ for every } i \quad (\text{i.e. } \|\tilde E\| \le \theta_0); \qquad \|\tilde E\|_1 \le \theta_0; \qquad \text{(T2)}\ \ \|\hat E\|_1 \le \frac{\theta_0}{a\,L}.$$
--   (T1) is delivered in the exact eigenvalue shape consumed by the Weyl-inequality lemma `RHLinalg.weyl_posIndexAbove_le`; (T2) is the paper's "Moreover the trace norm satisfies $\|\hat E\|_1 \le \theta_0/(aL)$" (the further "$\le 2\theta_0/L$" follows from $a \ge 1/2$, proved elsewhere).
--
--   **Role.** This is the tail proposition [prop:tail] of §4.2 for the concrete objects of `Zeta23/Defs.lean`; `eventually_tailInputs` packages it into the eventually-in-$T$ form used by the main theorem.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L442-L478, docstring tag [prop:tail]

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne

open Matrix Finset Complex
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg
variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

theorem Zeta23.Tail.prop_tail {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ} (H : TailHyp Z P T A₀ C₁)
    (ha : 0 < P.a T)
    (hEt : (P.tilde T (Z.Ez P T)).IsHermitian) (hEh : (P.hat T (Z.Ez P T)).IsHermitian) :
    (∀ i, |hEt.eigenvalues i| ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T) ∧
    traceNorm hEt ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T ∧
    traceNorm hEh ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T) := by sorry
