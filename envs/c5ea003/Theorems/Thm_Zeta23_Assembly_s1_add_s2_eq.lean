-- Prove2me | Theorems.Thm_Zeta23_Assembly_s1_add_s2_eq
-- name    : Zeta23.Assembly.s1_add_s2_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:42:30.678735+00:00
-- url     : https://prove2.me/theorems/8c9b640b-3315-480e-a496-45716e64f162
-- title:
--   $s_1 + s_2 = N_0^*(T - D_0,\ 2T + D_0)$
-- statement:
--   Let $Z$ be an abstract zero configuration and $T$ a real height. Write $D_0 := \sqrt{T}$ and $I' := (T - D_0,\ 2T + D_0]$ for the slightly enlarged window, and let $\mathcal{Z}(I')$ be the set of distinct zeros with ordinate in $I'$. The paper's block decomposition splits the on-line part of $\mathcal{Z}(I')$ into $\mathcal{S}_1$ (zeros with $\beta = 1/2$ and multiplicity $m_\rho = 1$) and $\mathcal{S}_2$ ($\beta = 1/2$ and $m_\rho \ge 2$), with cardinalities $s_1 := \#\mathcal{S}_1$ and $s_2 := \#\mathcal{S}_2$.
--
--   The theorem asserts the exact counting identity
--   $$s_1 + s_2 \;=\; N_0^*(T - D_0,\ 2T + D_0),$$
--   where $N_0^*$ counts *distinct* on-line zeros in the window (without multiplicity). Indeed $\mathcal{S}_1 \cup \mathcal{S}_2$ is exactly $\mathcal{Z}(I') \cap \{\beta = 1/2\}$, since every zero has $m_\rho \ge 1$, and the union is disjoint.
--
--   This identity lets the seam inequality `seamA` convert the rank/positivity bound $4\,\mathrm{tr}\,\hat A - \lVert\hat A\rVert_F^2 \le 2(s_1 + s_2) + \dots$, whose right side is phrased in block data, into a bound on the zero-counting function $N_0^*$ that Theorem A is about.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L949-L972

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
open Set
variable (Z : ZeroConfig)
variable (T : ℝ)
variable {T}

theorem Zeta23.Assembly.s1_add_s2_eq : Z.s1 T + Z.s2 T = Z.N0star (T - D0 T) (2 * T + D0 T) := by sorry
