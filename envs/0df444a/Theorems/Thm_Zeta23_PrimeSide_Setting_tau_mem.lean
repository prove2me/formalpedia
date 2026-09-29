-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_Setting_tau_mem
-- name    : Zeta23.PrimeSide.Setting.tau_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:07:25.896884+00:00
-- url     : https://prove2.me/theorems/7c1a9e86-134e-4596-b303-79c2e3540cfb
-- title:
--   Grid points stay in the window: $T \le \tau_k \le 2T$ for $k < d$
-- statement:
--   Let $p$ be a parameter setting with height $T$, window length $L$, grid spacing $h = 2\pi/L$, grid size $d = \lfloor LT/2\pi\rfloor$ and grid points $\tau_k = T + kh$ [eq:fk].
--
--   The theorem asserts that if $L > 0$ and $T \ge 0$, then for every natural number $k < d$,
--   $$T \;\le\; \tau_k \;\le\; 2T.$$
--   The lower bound is immediate from $kh \ge 0$; the upper bound holds because $k \le d - 1$ and $dh \le T$ by the choice $d = \lfloor LT/2\pi\rfloor = \lfloor T/h\rfloor$.
--
--   This basic location fact is used throughout the prime side: by `prop_trace_mu` (grid points sampled inside $I = [T,2T]$ in the trace asymptotics), and by `dom_right`, `majK2_integrable` and `setIntegral_compl_sqI_majK2_le` in the domination and tail arguments.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1367-L1381

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

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.Setting.tau_mem (p : Setting) (hL : 0 < p.L) (hT : 0 ≤ p.T) {k : ℕ} (hk : k ∈ Finset.range p.d) :
    p.T ≤ p.tau k ∧ p.tau k ≤ 2 * p.T := by sorry
