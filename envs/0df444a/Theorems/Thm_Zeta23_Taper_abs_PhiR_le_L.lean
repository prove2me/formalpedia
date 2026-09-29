-- Prove2me | Theorems.Thm_Zeta23_Taper_abs_PhiR_le_L
-- name    : Zeta23.Taper.abs_PhiR_le_L
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:29:37.109841+00:00
-- url     : https://prove2.me/theorems/54c53ebb-36f2-4b3b-93d4-7e0978e7107d
-- title:
--   Uniform bound $|\Phi(r)| \le L$ for the transform of $\varphi^2$
-- statement:
--   **Setup.** Let $\varrho$ be a taper profile ($C^3$, monotone, $\varrho = 0$ on $(-\infty,0]$, $\varrho = 1$ on $[1,\infty)$), and let $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$ be the associated taper with $0 < w$ and $2w \le L$. Following [eq:PhigA], $\Phi := \widehat{\varphi^2}$ is the paper Fourier transform $\Phi(z) = \int \varphi(u)^2 e^{izu}\,du$, and `PhiR ϱ L w r` $:= \operatorname{Re}\Phi(r)$ is its restriction to the real line as a real number (that $\Phi$ is real on $\mathbb{R}$ is proved separately, not assumed).
--
--   **Statement.** For every real $r$,
--   $$|\Phi(r)| \;\le\; L.$$
--   This is the trivial bound $|\Phi(r)| \le \int \varphi^2 \le L$, using $0 \le \varphi \le 1$ and $\operatorname{supp}\varphi \subseteq [-L/2, L/2]$.
--
--   **Role.** One of the three bounds ($|\Phi| \le L$, $|\Phi(r)|\,|r| \le 2$, $|\Phi(r)|\,r^2 \le c_\varrho/w$) that assemble into the envelope $\psi$ of [eq:psidef] controlling $\Phi$ on the real line. It is consumed by `Zeta23.PrimeSide.localHyps_concrete`, which instantiates the prime-side hypotheses for the concrete taper in the mollified second-moment computation.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L328-L340

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Taper_Basic

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.abs_PhiR_le_L (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |PhiR ϱ L w r| ≤ L := by sorry
