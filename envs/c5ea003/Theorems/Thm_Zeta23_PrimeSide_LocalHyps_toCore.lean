-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_LocalHyps_toCore
-- name    : Zeta23.PrimeSide.LocalHyps.toCore
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:01:02.073303+00:00
-- url     : https://prove2.me/theorems/747a6b0f-0692-4bad-a60e-55699e958428
-- title:
--   Flat-top taper data satisfy the window-generic core hypotheses
-- statement:
--   `LocalHyps` $c_\varrho\ p\ F$ is the full package of facts about the flat-top taper family used in §5: profile constant $c_\varrho \ge 4$, parameter ranges $0<\lambda\le1$ and $1 \le w \le L/8$, the majorant bounds $|\hat\varphi|, |\Phi| \le \psi := \min(L,\,2/|r|,\,c_\varrho/(wr^2))$ with their integral consequences, the Fourier identities and Poisson summation, and — specific to the flat-top window — the plateau lower bound $(L - 2w - |y|)_+ \le g(y)$ and $1 - 2w/L \le b$ from [eq:abdef]. `LocalHypsCore` is the window-generic weakening in which these last two are replaced by $g \ge 0$ and $b \ge 1/2$ (which also hold for the Montgomery–Taylor window).
--
--   The theorem states that every datum satisfying `LocalHyps` satisfies `LocalHypsCore`: indeed $w \le L/8$ [eq:wrange] gives $b \ge 1 - 2w/L \ge 3/4 \ge 1/2$, and $g(y) \ge (L-2w-|y|)_+ \ge 0$.
--
--   This is the bridge letting every Core-typed result of §5 apply to the concrete flat-top taper; it is consumed by `concreteFacts` when the abstract prime-side machinery is instantiated.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L448-L501, docstring tags [eq:abdef], [eq:wrange]

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

theorem Zeta23.PrimeSide.LocalHyps.toCore {cϱ : ℝ} {p : Setting} {F : LocalFun} (hF : LocalHyps cϱ p F) :
    LocalHypsCore cϱ p F := by sorry
