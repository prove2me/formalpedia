-- Prove2me | Theorems.Thm_ZOGlobalLB_Supplement_theorem_2_5
-- name    : ZOGlobalLB.Supplement.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:51:42.972176+00:00
-- url     : https://prove2.me/theorems/d0cb4aa9-7b70-4365-88ff-dc4b1aa7853d
-- title:
--   Theorem 2.5 — two-level gap amplification
-- statement:
--   There are universal constants $c,c_\varepsilon,C_*,C>0$ such that
--
--   $$
--   \varepsilon\le c_\varepsilon L_0,
--   \qquad \Delta H\ge C_*L_0^2,
--   \qquad d\ge C\frac{L_0^2}{\varepsilon^2}\log\!\left(2+\frac{L_0^2}{\varepsilon^2}\right)
--   $$
--
--   imply that every randomized adaptive reusable-label algorithm succeeding with probability at least $2/3$ on every admissible instance has expected query cost at least
--
--   $$
--   c\frac{dL_0^2}{\varepsilon^4}\min\!\left\{\Delta H,\frac{L_0^4}{\varepsilon^2}\right\}
--   $$
--
--   on some finite family.
--
--   Differences from the source:
--   - encoding: finite labels and expected query cost under the standing oracle convention → `Fin n` and an extended-nonnegative lintegral of the published stopping cost; reason: preserves arbitrary reuse and nontermination without changing any instance
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem 2.5, p.5, Eqs. (9)-(10)

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible
import Definitions.Def_ZOGlobalLB_ZOAlg

open MeasureTheory
open scoped ENNReal

universe u

namespace ZOGlobalLB

namespace Supplement

/-- **Theorem 2.5 (Two-level).** Xia, Yuan,
*On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*, arXiv:2610.19652,
Theorem 2.5, p.5, (9)--(10).

There are universal positive `c, cε, Cstar, C` such that the three displayed conditions imply
the full two-level expected query lower bound
`c d L₀² / ε⁴ * min {ΔH, L₀⁴/ε²}` for every successful randomized adaptive reusable-label
algorithm.

**Formalization Note.** The quantifier order is universal constants, problem data, algorithm,
then its hard family. The minimum is retained with both branches; no large-gap branch is dropped. -/
theorem theorem_2_5 :
    ∃ c cε Cstar C : ℝ,
      0 < c ∧ 0 < cε ∧ 0 < Cstar ∧ 0 < C ∧
      ∀ (d : ℕ) (L₀ Δ H ε : ℝ), 0 < L₀ → 0 < Δ → 0 < H → 0 < ε →
        ε ≤ cε * L₀ → Cstar * L₀ ^ 2 ≤ Δ * H →
        C * (L₀ ^ 2 / ε ^ 2) * Real.log (2 + L₀ ^ 2 / ε ^ 2) ≤ (d : ℝ) →
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : ∀ n : ℕ, ZOAlg d n Ω),
          (∀ (n : ℕ) (F : Fin n → E d → ℝ), Admissible Δ H L₀ F →
              (2 / 3 : ℝ≥0∞) ≤ μ {ω | (A n).Succeeds ε F ω}) →
          ∃ (n : ℕ) (F : Fin n → E d → ℝ), Admissible Δ H L₀ F ∧
            ENNReal.ofReal
                (c * d * L₀ ^ 2 / ε ^ 4 * min (Δ * H) (L₀ ^ 4 / ε ^ 2)) ≤
              ∫⁻ ω, ((A n).cost F ω : ℝ≥0∞) ∂μ := by sorry

end Supplement

end ZOGlobalLB
