-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_inner_sub_le
-- name    : Zeta23.PrimeSide.abs_inner_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:12:59.117251+00:00
-- url     : https://prove2.me/theorems/51603ed8-db06-486a-b2bf-ddfdb24fba7a
-- title:
--   Shear-integral stability of $\int_I \mu^2$: $\bigl|\int_{I_x} \mu(x+\tau')\mu(\tau') - \int_I \mu^2\bigr| \le (1+K)l^2|x| + 10\,l\,x^2$
-- statement:
--   Here $\mu(\tau) = \tfrac{1}{2\pi}\,\mathrm{Re}\,\tfrac{\Gamma'}{\Gamma}\bigl(\tfrac14 + \tfrac{i\tau}{2}\bigr) - \tfrac{\log \pi}{2\pi}$ is the archimedean density [eq:mudef] (formalized via Mathlib's `Complex.digamma`), $I = [T, 2T]$, and $I_x = I \cap (I - x) = [\max(T-x, T),\, \min(2T-x, 2T)]$ is the sheared window. The hypotheses are: the $\Gamma$-facts package H-Γ (`Zeta23.GammaFacts`), the window-generic taper facts `LocalHypsCore`, $T \ge 2$, the sup bound $|\mu(\tau)| \le l$ on $I$ (where $l = \log(T/2\pi)$), and an increment bound with constant $K \ge 0$: for all $t \ge 2$ and all $r \in \mathbb{R}$,
--   $$|\mu(t + r) - \mu(t)| \;\le\; \frac{K|r| + 10 r^2}{t}.$$
--   The conclusion is the core scalar estimate: for every $x \in \mathbb{R}$,
--   $$\Bigl|\int_{I_x} \mu(x + \tau')\, \mu(\tau')\, d\tau' \;-\; \int_I \mu(\tau')^2\, d\tau'\Bigr| \;\le\; (1 + K)\, l^2\, |x| + 10\, l\, x^2.$$
--   The proof splits into replacing $\mu(x + \tau')$ by $\mu(\tau')$ on $I_x$ (increment bound, window length $\le T$, $\tau' \ge T$) and completing $I_x$ to $I$ (the omitted set has measure $\min(|x|, T)$ and $\mu^2 \le l^2$ there).
--
--   It is the inner-integral input to `mumu_core`, the evaluation $\mathcal{M}[\mu,\mu] = 2\pi b L \int_T^{2T} \mu^2 + O(l^2 \log L)$ of [prop:mumu] (module `Zeta23.PrimeSideA.MuMu`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/MuMu.lean#L39-L157

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
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ}
variable {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.abs_inner_sub_le (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) (hT2 : 2 ≤ p.T)
    (hμl : ∀ τ ∈ Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hKinc : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    (x : ℝ) :
    |(∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
        - ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2|
      ≤ (1 + K) * p.l ^ 2 * |x| + 10 * p.l * x ^ 2 := by sorry
