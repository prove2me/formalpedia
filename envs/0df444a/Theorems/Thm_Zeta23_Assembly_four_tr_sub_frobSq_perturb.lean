-- Prove2me | Theorems.Thm_Zeta23_Assembly_four_tr_sub_frobSq_perturb
-- name    : Zeta23.Assembly.four_tr_sub_frobSq_perturb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:41:50.986695+00:00
-- url     : https://prove2.me/theorems/a4d00678-0450-4f09-a1d2-3ce796dbb829
-- title:
--   Perturbation of $4\,\mathrm{tr}\,\hat{A} - \lVert\hat{A}\rVert_F^2$ under a trace-norm-bounded error
-- statement:
--   A purely linear-algebraic perturbation lemma (the perturbation step in the paper's proof of [prop:zeroside-rank]). Let $\hat G, \hat A, \hat E$ be square matrices over $\mathbb{R}$ or $\mathbb{C}$ with $\hat G = \hat A + \hat E$. Here $\mathrm{tr}$ denotes the real part of the trace (`rtrace`) and $\lVert M \rVert_F^2 = \operatorname{Re}\mathrm{tr}(M^* M)$ the squared Frobenius norm (`frobSq`). Suppose $B \ge 0$ is a common bound for the error in the sense that $|\mathrm{tr}\,\hat E| \le B$ and $\lVert \hat E \rVert_F^2 \le B^2$.
--
--   Then
--   $$4\,\mathrm{tr}\,\hat G - \lVert \hat G \rVert_F^2 - B\left(4 + 2\lVert \hat G \rVert_F + B\right) \;\le\; 4\,\mathrm{tr}\,\hat A - \lVert \hat A \rVert_F^2.$$
--
--   This makes explicit the paper's $O(\theta_0 L^{-1}(1 + \lVert\hat G\rVert_F))$ loss: with $\hat A = \hat G - \hat E$, one has $\mathrm{tr}\,\hat A \ge \mathrm{tr}\,\hat G - B$ and $\lVert\hat A\rVert_F \le \lVert\hat G\rVert_F + B$, and expanding gives exactly the loss $B(4 + 2\lVert\hat G\rVert_F + B)$. In the application (Seam A, hat units), $\hat G$ is the full zero-side matrix, $\hat A$ its truncation to zeros with ordinate in $I'$, $\hat E$ the tail, and prop:tail supplies $B = \lVert\hat E\rVert_1 \le 2\theta_0/L$. Consumed by `seamA`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L143-L165, docstring tag [prop:zeroside-rank]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Assembly
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_TracesBoundsE

open Matrix Finset RHLinalg
open scoped ComplexOrder
open Zeta23
open Assembly
open scoped Matrix.Norms.Frobenius
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n]

theorem Zeta23.Assembly.four_tr_sub_frobSq_perturb {Ghat Ahat Ehat : Matrix n n 𝕜}
    (hGAE : Ghat = Ahat + Ehat) {B : ℝ} (hB : 0 ≤ B)
    (htrE : |rtrace Ehat| ≤ B) (hfrE : frobSq Ehat ≤ B ^ 2) :
    4 * rtrace Ghat - frobSq Ghat - B * (4 + 2 * Real.sqrt (frobSq Ghat) + B)
      ≤ 4 * rtrace Ahat - frobSq Ahat := by sorry
