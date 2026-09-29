-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_prop_PP
-- name    : Zeta23.PrimeSide.prop_PP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:24:23.534424+00:00
-- url     : https://prove2.me/theorems/b067d0cf-3edd-4929-b3b9-8ba6f7985908
-- title:
--   [prop:PP]: $\mathcal{M}[P_X,P_X] = \tfrac{T}{\pi}\sum_{n\le X}\tfrac{\Lambda(n)^2}{n}\,g(\log n) + O(L^2X)$
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $l=\log(T/2\pi)$, $L=\lambda l$, $X=e^L$, window $I=[T,2T]$, and taper data $F=(\hat\varphi,\Phi,A_\varphi,g,a,b)$. The prime-power density is $P_X(\tau)=-\tfrac{1}{\pi}\sum_{n\le X}\Lambda(n)n^{-1/2}\cos(\tau\log n)$ [eq:Pdef] ($\Lambda$ the von Mangoldt function, the sum over integers $0<n\le\lfloor X\rfloor$), the seam form is $\mathcal{M}[u_1,u_2]=\iint_{I\times I}\Phi(\tau-\tau')^2u_1(\tau)u_2(\tau')\,d\tau\,d\tau'$, and the main-term sum is $\sum_{n\le X}\Lambda(n)^2/n\cdot g(\log n)$ with $g=\varphi^2\star\varphi^2$ the taper correlation.
--
--   Assume the Chebyshev–Mertens estimates H-cheb, the Montgomery–Vaughan weighted Hilbert inequality H-MV with some constant $C>0$, and $0<\lambda\le 1$. Then there is a constant $C'$ such that uniformly for large $T$ — i.e. there is $T_0$ with the following for every setting $p$ at bandwidth ratio $\lambda$, $T\ge T_0$, and taper $F$ satisfying `LocalHypsCore` —
--   $$\Bigl|\mathcal{M}[P_X,P_X]-\frac{T}{\pi}\sum_{n\le X}\frac{\Lambda(n)^2}{n}\,g(\log n)\Bigr|\ \le\ C'\,L^2X.$$
--
--   This is [prop:PP] in its first form (§5.4), the prime–prime block of the second-moment evaluation of $\mathcal{M}$: the diagonal $n=m$ gives the main term, and the off-diagonal is $\ll L^2X$ by H-MV with weights $\delta_n=1/(2n)$ [eq:deltan] and $\sum_{n\le X}\Lambda(n)^2\ll X\log X$. Its consumer is `concreteFacts` (module `Zeta23.PrimeSideB.PP`), the bundle feeding the trace assembly [thm:traces].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PP.lean#L327-L460, docstring tag [prop:PP]

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
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PP
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ lam : ℝ}

theorem Zeta23.PrimeSide.prop_PP (hcheb : Zeta23.ChebyshevMertens) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PX p.X) - p.T / π * sumA2g p.X F.g|
        ≤ C * (p.L ^ 2 * p.X)) := by sorry
