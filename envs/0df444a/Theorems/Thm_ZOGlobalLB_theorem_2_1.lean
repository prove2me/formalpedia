-- Prove2me | Theorems.Thm_ZOGlobalLB_theorem_2_1
-- name    : ZOGlobalLB.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:48:07.967092+00:00
-- url     : https://prove2.me/theorems/4c19f373-f92f-4d79-b2f1-a8f35d54f159
-- title:
--   Theorem 2.1 — basic global stochastic lower bound $N\ge c\,dL_0^2\min\{\Delta H,L_0^2\}/\epsilon^4$
-- statement:
--   There are universal constants $c,C,c_0>0$ such that the following holds. Let $B=\min\{\Delta H,L_0^2\}$ with $L_0,\Delta,H,\epsilon>0$, and suppose
--   $$\epsilon^2\le c_0B,\qquad d\ge C\,\frac{B}{\epsilon^2}\log\Bigl(2+\frac{BL_0^2}{\epsilon^4}\Bigr).$$
--   Let an algorithm be randomized and adaptive, with exact scalar evaluations $f_\xi(x)$ of any label at any point, label reuse and an arbitrary output. If it finds a point with $\|\nabla f(\hat x)\|\le\epsilon$ with probability at least $2/3$ on every instance of the class (2), then on some instance of (2) its expected number of evaluations is at least
--   $$c\,\frac{dL_0^2B}{\epsilon^4}.$$
--
--   The dimension cost and the accuracy cost multiply: this matches the known $O(d\epsilon^{-4})$ upper rate of zeroth-order methods in $d$ and $\epsilon$.
--
--   Differences from the source:
--   - reading: N ≥ c dL₀²B/ε⁴ in (5) → worst-case expected query cost; reason: p.4: 'Throughout, lower bounds concern worst-case expected query cost for success probability at least 2/3 on every admissible instance'
--   - encoding: worst-case expected cost on some instance → ∃ an admissible family with expected cost ≥ c dL₀²B/ε⁴; reason: implies the supremum form
--   - encoding: a randomized adaptive algorithm → a family ZOAlg d n Ω over the label count n, seeds from a probability space (Ω, μ); reason: the family may depend on the algorithm (p.4), so the algorithm knows the public label set
--   - encoding: success and cost → ZOAlg.Succeeds (stop with ‖∇f(x̂)‖ ≤ ε) and ZOAlg.cost in ℕ∪{∞}; reason: a run that never stops fails and costs ∞
--   - encoding: a randomized adaptive algorithm → a rule jointly measurable in the seed and the history (measurable_next); reason: the run must be a random element for its probabilities and expected cost to be defined; nothing else is imposed
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem 2.1, p.4, (2)–(5)

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible
import Definitions.Def_ZOGlobalLB_ZOAlg

open MeasureTheory
open scoped ENNReal

universe u

namespace ZOGlobalLB

/-- **Theorem 2.1 (Basic global stochastic lower bound).** Xia, Yuan, *On Global Joint Lower
Bounds in Zeroth-Order Nonconvex Optimization*, arXiv:2610.19652, Theorem 2.1, p.4, (3)–(5).

There are universal constants `c, C, c₀ > 0` such that, with `B = min{ΔH, L₀²}`, whenever
`ϵ² ≤ c₀B` and `d ≥ C (B/ϵ²) log(2 + BL₀²/ϵ⁴)`, every randomized adaptive algorithm that finds
`‖∇f(x̂)‖ ≤ ϵ` with probability at least `2/3` on every instance of the class (2) has expected
query cost at least `c d L₀² B / ϵ⁴` on some instance of (2).

**Formalization Note.**
* The constants are quantified first, then `d, L₀, Δ, H, ϵ`, then the algorithm, then the hard
  family: the family may depend on the algorithm (p.4).
* An algorithm is a family `A n : ZOAlg d n Ω` over the size `n` of the public label set, with
  an arbitrary probability space of seeds `(Ω, μ)`.
* Success is `ZOAlg.Succeeds` (stop, and output an `ϵ`-stationary point of the population mean);
  cost is `ZOAlg.cost : ℕ∞` (`⊤` for a run that never stops). "Worst-case expected query cost"
  (p.4) is witnessed by one family `F`, which implies the supremum form.
* `Admissible Δ H L₀ F` is the class (2). -/
theorem theorem_2_1 :
    ∃ c C c₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < c₀ ∧
      ∀ (d : ℕ) (L₀ Δ H ε : ℝ), 0 < L₀ → 0 < Δ → 0 < H → 0 < ε →
        ε ^ 2 ≤ c₀ * min (Δ * H) (L₀ ^ 2) →
        C * (min (Δ * H) (L₀ ^ 2) / ε ^ 2) *
            Real.log (2 + min (Δ * H) (L₀ ^ 2) * L₀ ^ 2 / ε ^ 4) ≤ (d : ℝ) →
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : ∀ n : ℕ, ZOAlg d n Ω),
          (∀ (n : ℕ) (F : Fin n → E d → ℝ), Admissible Δ H L₀ F →
              (2 / 3 : ℝ≥0∞) ≤ μ {ω | (A n).Succeeds ε F ω}) →
          ∃ (n : ℕ) (F : Fin n → E d → ℝ), Admissible Δ H L₀ F ∧
            ENNReal.ofReal (c * d * L₀ ^ 2 * min (Δ * H) (L₀ ^ 2) / ε ^ 4) ≤
              ∫⁻ ω, ((A n).cost F ω : ℝ≥0∞) ∂μ := by sorry

end ZOGlobalLB
