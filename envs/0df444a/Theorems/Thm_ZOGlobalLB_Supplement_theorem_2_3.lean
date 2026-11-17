-- Prove2me | Theorems.Thm_ZOGlobalLB_Supplement_theorem_2_3
-- name    : ZOGlobalLB.Supplement.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:51:01.350849+00:00
-- url     : https://prove2.me/theorems/2057fb1e-9823-4e58-9094-f0a483fa3e38
-- title:
--   Theorem 2.3 — randomized exact-value lower bound
-- statement:
--   There are universal constants $c,C,c_0>0$ such that, with $B=\min\{\Delta H,L_0^2\}$, if
--
--   $$
--   \varepsilon^2\le c_0B,
--   \qquad
--   d\ge C\frac{B}{\varepsilon^2}\log\!\left(2+\frac{B}{\varepsilon^2}\right),
--   $$
--
--   then every randomized adaptive exact-value algorithm that finds an $\varepsilon$-stationary point with probability at least $2/3$ for every globally $L_0$-Lipschitz, $H$-smooth function with global initial gap at most $\Delta$ has expected cost at least
--
--   $$
--   c\,dB/\varepsilon^2
--   $$
--
--   on some such fixed function. Randomization, query locations, stopping, and outputs remain unrestricted.
--
--   Differences from the source:
--   - encoding: one fixed exact-value function → a `Fin 1` family queried by the published adaptive zeroth-order algorithm; reason: the unique public label carries no information and gives exactly the same oracle
--   - encoding: expected query count → an $[0,\infty]$-valued lintegral of an $\mathbb N\cup\{\infty\}$ stopping cost; reason: retains nontermination rather than assigning it a finite default
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem 2.3, p.5, Eq. (8)

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible
import Definitions.Def_ZOGlobalLB_ZOAlg

open MeasureTheory
open scoped ENNReal

universe u

namespace ZOGlobalLB

namespace Supplement

/-- **Theorem 2.3 (Exact-value lower bound).** Xia, Yuan,
*On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*, arXiv:2610.19652,
Theorem 2.3, p.5, (8).

For universal positive `c, C, c₀`, let `B = min {ΔH, L₀²}`. Under the printed accuracy and
dimension conditions, every randomized adaptive exact-value algorithm that succeeds with
probability at least `2/3` on every globally `L₀`-Lipschitz, `H`-smooth function of initial
gap at most `Δ` has expected cost at least `c d B / ε²` on some such function.

**Formalization Note.** A fixed function is represented by the singleton family `Fin 1`; thus
the public label carries no information, while `ZOAlg d 1 Ω` still permits arbitrary randomized
adaptive query points, stopping, and output. `Admissible` specialized to that singleton is exactly
the class in the theorem. -/
theorem theorem_2_3 :
    ∃ c C c₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < c₀ ∧
      ∀ (d : ℕ) (L₀ Δ H ε : ℝ), 0 < L₀ → 0 < Δ → 0 < H → 0 < ε →
        ε ^ 2 ≤ c₀ * min (Δ * H) (L₀ ^ 2) →
        C * (min (Δ * H) (L₀ ^ 2) / ε ^ 2) *
            Real.log (2 + min (Δ * H) (L₀ ^ 2) / ε ^ 2) ≤ (d : ℝ) →
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : ZOAlg d 1 Ω),
          (∀ f : E d → ℝ, Admissible Δ H L₀ (fun _ : Fin 1 => f) →
              (2 / 3 : ℝ≥0∞) ≤ μ {ω | A.Succeeds ε (fun _ : Fin 1 => f) ω}) →
          ∃ f : E d → ℝ, Admissible Δ H L₀ (fun _ : Fin 1 => f) ∧
            ENNReal.ofReal (c * d * min (Δ * H) (L₀ ^ 2) / ε ^ 2) ≤
              ∫⁻ ω, (A.cost (fun _ : Fin 1 => f) ω : ℝ≥0∞) ∂μ := by sorry

end Supplement

end ZOGlobalLB
