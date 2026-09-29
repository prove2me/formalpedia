-- Prove2me | Theorems.Thm_Zeta23_Assembly_seamA
-- name    : Zeta23.Assembly.seamA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:42:36.866839+00:00
-- url     : https://prove2.me/theorems/9b2512f9-e66d-4a09-b9c9-abc39a313a2c
-- title:
--   Seam A: explicit zero-side lower bound for $N_0^*(T,2T)$
-- statement:
--   The explicit form of [eq:zeroside-rank] for the concrete matrices of the proof. Let $Z$ be an abstract zero configuration, $P$ a parameter pack, and $T \ge 0$. Write $\hat G := $ `P.hat T (Z.Gz P T)` for the zero-side Gram matrix $G_{kl} = \sum_\rho m_\rho\, \hat\varphi(\gamma_\rho - \tau_k)\, \hat\varphi(\gamma_\rho - \tau_l)$ rescaled to hat units ($M \mapsto M/(aL^2)$); $\mathrm{tr}$ and $\lVert\cdot\rVert_F$ are the real trace and Frobenius norm; $N(T,2T)$ is the zero count with multiplicity; $N(I' \setminus I) := N(T{-}D_0, T) + N(2T, 2T{+}D_0)$ is the boundary count with $D_0 = \sqrt T$; and $B_0 := \theta_0/(aL)$ is the tail trace-norm bound.
--
--   Assume the block inputs of prop:block (the decomposition $\hat A = P + Q$ with $P \succeq 0$, rank and trace bounds, and the counts [eq:Ncount], produced by `ZeroSide.lean`) and the tail inputs of prop:tail (eigenvalue bound $\theta_0$ for $\tilde E$ and trace-norm bound for $\hat E$, produced by `Tail.lean`), together with $a, L > 0$. Then
--   $$4\,\mathrm{tr}\,\hat G - \lVert\hat G\rVert_F^2 - 2 N(T,2T) - 3 N(I'\setminus I) - B_0\left(4 + 2\lVert\hat G\rVert_F + B_0\right) \;\le\; N_0^*(T, 2T),$$
--   where $N_0^*(T,2T)$ counts distinct on-line zeros with ordinate in $(T, 2T]$.
--
--   This is the seam where the linear-algebra chapter (positivity index, rank bounds, tail perturbation `four_tr_sub_frobSq_perturb`, and the counting identity `s1_add_s2_eq`) is stitched into a single explicit inequality; `thmA_abstract_err` combines it with the trace asymptotics [thm:traces] to prove Theorem A at fixed $\lambda$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L1029-L1052, docstring tag [eq:zeroside-rank]

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
variable (Z : ZeroConfig) (P : Params) (T : ℝ)
variable {Z P T}

theorem Zeta23.Assembly.seamA (hT : 0 ≤ T) (hB : BlockInputs Z P T) {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀)
    (ha : 0 < P.a T) (hL : 0 < P.L T) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T) * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ Z.N0star T (2 * T) := by sorry
