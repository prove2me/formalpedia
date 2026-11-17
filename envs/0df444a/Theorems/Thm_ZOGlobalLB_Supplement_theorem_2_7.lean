-- Prove2me | Theorems.Thm_ZOGlobalLB_Supplement_theorem_2_7
-- name    : ZOGlobalLB.Supplement.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:52:05.825482+00:00
-- url     : https://prove2.me/theorems/25a49521-0bcb-4533-8a31-16164fbb0b54
-- title:
--   Theorem 2.7 — logarithmic dependence on the global gap
-- statement:
--   There are universal positive constants $c,c_\varepsilon,C_0,C$ and $C_1>1$ such that, if $\varepsilon\le c_\varepsilon L_0$, $\Delta H\ge C_0L_0^2$, and
--
--   $$
--   K=1+\left\lfloor\frac{\log(\Delta H/(C_0L_0^2))}{\log C_1}\right\rfloor,
--   \qquad
--   d\ge C\left[\frac{L_0^2}{\varepsilon^2}\log\!\left(2+\frac{L_0^2}{\varepsilon^2}\right)+\log(2K)\right],
--   $$
--
--   then every successful randomized adaptive reusable-label algorithm has expected cost at least
--
--   $$
--   c\frac{dL_0^4}{\varepsilon^4}\left[1+\log\frac{\Delta H}{C_0L_0^2}\right]
--   $$
--
--   on some admissible finite family.
--
--   Differences from the source:
--   - encoding: the floor-defined positive nesting depth $K$ → one plus Lean's natural floor of the same nonnegative real ratio; reason: $\Delta H\ge C_0L_0^2$ and $C_1>1$ make the two floors identical
--   - encoding: finite labels and expected query cost → `Fin n` and an extended-nonnegative lintegral of the published stopping cost; reason: preserves label reuse and nontermination
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem 2.7, p.6, Eqs. (12)-(13)

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible
import Definitions.Def_ZOGlobalLB_ZOAlg

open MeasureTheory
open scoped ENNReal

universe u

namespace ZOGlobalLB

namespace Supplement

/-- **Theorem 2.7 (Logarithmic gap).** Xia, Yuan,
*On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*, arXiv:2610.19652,
Theorem 2.7, p.6, (12)--(13).

There are universal positive `c, cε, C₀, C` and `C₁ > 1` such that, for the exact nesting
depth `K = 1 + floor(log(ΔH/(C₀L₀²))/log C₁)`, the printed conditions imply the expected query
lower bound `c d L₀⁴ ε⁻⁴ [1 + log(ΔH/(C₀L₀²))]`.

**Formalization Note.** `⌊·⌋₊` is the natural floor; the large-gap and `C₁ > 1` hypotheses make
its argument nonnegative. The `log(2K)` term and the complete logarithmic factor in the conclusion
are both retained. -/
theorem theorem_2_7 :
    ∃ c cε C₀ C C₁ : ℝ,
      0 < c ∧ 0 < cε ∧ 0 < C₀ ∧ 0 < C ∧ 1 < C₁ ∧
      ∀ (d : ℕ) (L₀ Δ H ε : ℝ), 0 < L₀ → 0 < Δ → 0 < H → 0 < ε →
        ε ≤ cε * L₀ → C₀ * L₀ ^ 2 ≤ Δ * H →
        let K : ℕ := 1 + ⌊Real.log (Δ * H / (C₀ * L₀ ^ 2)) / Real.log C₁⌋₊
        C * ((L₀ ^ 2 / ε ^ 2) * Real.log (2 + L₀ ^ 2 / ε ^ 2) +
            Real.log (2 * K)) ≤ (d : ℝ) →
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : ∀ n : ℕ, ZOAlg d n Ω),
          (∀ (n : ℕ) (F : Fin n → E d → ℝ), Admissible Δ H L₀ F →
              (2 / 3 : ℝ≥0∞) ≤ μ {ω | (A n).Succeeds ε F ω}) →
          ∃ (n : ℕ) (F : Fin n → E d → ℝ), Admissible Δ H L₀ F ∧
            ENNReal.ofReal (c * d * L₀ ^ 4 / ε ^ 4 *
                (1 + Real.log (Δ * H / (C₀ * L₀ ^ 2)))) ≤
              ∫⁻ ω, ((A n).cost F ω : ℝ≥0∞) ∂μ := by sorry

end Supplement

end ZOGlobalLB
