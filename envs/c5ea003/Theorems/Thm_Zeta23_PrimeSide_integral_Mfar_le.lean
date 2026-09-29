-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_integral_Mfar_le
-- name    : Zeta23.PrimeSide.integral_Mfar_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:16:20.611883+00:00
-- url     : https://prove2.me/theorems/7360f7af-5848-4c44-bd57-c67e107d5de5
-- title:
--   Far half-line integral of the majorant: $\int_{2T}^{\infty} M_{\mathrm{far}} \le (d/T)(c_\varrho/w)(B/2+4)$
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $l=\log(T/2\pi)$, $L=\lambda l$, $d=\lfloor LT/2\pi\rfloor$ grid points, and taper data $F$ satisfying the window-generic core hypotheses with profile constant $c_\varrho$. For a level $B$, the far majorant (used for distances $\Delta$ beyond $2T$ from the window, §5.3) is
--   $$M_{\mathrm{far}}(\Delta)\ :=\ d\cdot\frac{c_\varrho}{w\,\Delta^2}\Bigl(B+2\sqrt{\Delta/T}\Bigr).$$
--
--   Assume $B\ge 0$ and $T\ge 1$. Then
--   $$\int_{2T}^{\infty} M_{\mathrm{far}}(\Delta)\,d\Delta\ \le\ \frac{d}{T}\cdot\frac{c_\varrho}{w}\Bigl(\frac{B}{2}+4\Bigr).$$
--
--   This is the far-range half of the grid bound N2 of §5.3 (module `Zeta23.PrimeSideA.EndsNu`): it is combined with the near-range estimate `integral_Mnear_le` in `nu_grid_bound_raw`, which controls $\int_{\tau\notin I}|\nu|\,\sigma$ for the $\mathcal{E}_2$ error of the end-effects lemma [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L524-L569

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsNu

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.integral_Mfar_le (hF : LocalHypsCoreW cϱ p F) (hB : 0 ≤ B) (hT : 1 ≤ p.T) :
    ∫ Δ in Ioi (2 * p.T), Mfar cϱ p B Δ ≤ p.d / p.T * (cϱ / p.w) * (B / 2 + 4) := by sorry
