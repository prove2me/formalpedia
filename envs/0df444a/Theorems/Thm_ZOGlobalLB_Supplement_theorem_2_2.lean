-- Prove2me | Theorems.Thm_ZOGlobalLB_Supplement_theorem_2_2
-- name    : ZOGlobalLB.Supplement.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:50:39.753076+00:00
-- url     : https://prove2.me/theorems/f9b9fae7-035e-4cb7-aded-b7e8341d54fc
-- title:
--   Theorem 2.2 — stochastic Goldstein lower bound
-- statement:
--   There are universal constants $c,C,c_0>0$ such that the following holds. Let
--
--   $$
--   B_G=\min\{\Delta\varepsilon/\delta,L_0^2\}.
--   $$
--
--   If $\varepsilon^2\le c_0B_G$ and
--
--   $$
--   d\ge C\frac{B_G}{\varepsilon^2}\log\!\left(2+\frac{B_GL_0^2}{\varepsilon^4}\right),
--   $$
--
--   then every randomized adaptive scalar-query algorithm that may reuse labels and succeeds with probability at least $2/3$ on every globally Lipschitz, possibly nonsmooth admissible population objective has expected cost at least
--
--   $$
--   c\,dL_0^2\min\!\left\{\frac{\Delta}{\delta\varepsilon^3},\frac{L_0^2}{\varepsilon^4}\right\}
--   $$
--
--   on some finite family. Query points and outputs are unrestricted.
--
--   Differences from the source:
--   - encoding: a finite label set and expected query count → `Fin n` and an $[0,\infty]$-valued lintegral of an $\mathbb N\cup\{\infty\}$ stopping cost; reason: preserves label reuse, nontermination, and the exact worst-case expectation
--   - encoding: positive $L_0,\Delta,\delta,\varepsilon$ implicit in the displayed divisions and stationarity regime → stated explicitly; reason: excludes only undefined source inputs
--   - reading: display (6) writes the convex hull of nearby Clarke subgradients, while the proof uses the closed hull → the published closed Goldstein hull `GradSampling.Conv.epsSubdiff`; reason: this is the reading used explicitly in the paper's proof on p.78 and gives the standard Clarke--Goldstein subdifferential
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem 2.2, p.5, Eq. (7)

import Mathlib
import Definitions.Def_ZOGlobalLB_Supplement_GoldsteinAdmissible
import Definitions.Def_ZOGlobalLB_Supplement_SucceedsGoldstein

open MeasureTheory
open scoped ENNReal

universe u

namespace ZOGlobalLB

namespace Supplement

/-- **Theorem 2.2 (Stochastic Goldstein lower bound).** Xia, Yuan,
*On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*, arXiv:2610.19652,
Theorem 2.2, p.5, (7).

There are universal positive constants such that, with
`B_G = min {Δ ε / δ, L₀²}`, the two conditions (4) with `B_G` in place of `B` force every
randomized adaptive reusable-label scalar-query algorithm that succeeds with probability at
least `2/3` on the nonsmooth class to have expected cost at least
`c d L₀² min {Δ/(δ ε³), L₀²/ε⁴}` on some instance.

**Formalization Note.** The universal constants precede all problem data and the hard finite
family follows the algorithm. `GoldsteinAdmissible` contains no differentiability or smoothness
hypothesis. Labels may be reused and query points and outputs are unrestricted through `ZOAlg`.
The positive assumptions on `δ` and `ε` exclude the undefined divisions in the printed formula. -/
theorem theorem_2_2 :
    ∃ c C c₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < c₀ ∧
      ∀ (d : ℕ) (L₀ Δ δ ε : ℝ), 0 < L₀ → 0 < Δ → 0 < δ → 0 < ε →
        ε ^ 2 ≤ c₀ * min (Δ * ε / δ) (L₀ ^ 2) →
        C * (min (Δ * ε / δ) (L₀ ^ 2) / ε ^ 2) *
            Real.log (2 + min (Δ * ε / δ) (L₀ ^ 2) * L₀ ^ 2 / ε ^ 4) ≤ (d : ℝ) →
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : ∀ n : ℕ, ZOAlg d n Ω),
          (∀ (n : ℕ) (F : Fin n → E d → ℝ), GoldsteinAdmissible Δ L₀ F →
              (2 / 3 : ℝ≥0∞) ≤ μ {ω | SucceedsGoldstein δ ε (A n) F ω}) →
          ∃ (n : ℕ) (F : Fin n → E d → ℝ), GoldsteinAdmissible Δ L₀ F ∧
            ENNReal.ofReal
                (c * d * L₀ ^ 2 * min (Δ / (δ * ε ^ 3)) (L₀ ^ 2 / ε ^ 4)) ≤
              ∫⁻ ω, ((A n).cost F ω : ℝ≥0∞) ∂μ := by sorry

end Supplement

end ZOGlobalLB
