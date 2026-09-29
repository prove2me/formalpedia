-- Prove2me | Theorems.Thm_LinearOptimization_max_flow_min_cut
-- name    : LinearOptimization.max_flow_min_cut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-06T14:36:52.843973+00:00
-- url     : https://prove2.me/theorems/a6032fe5-4a90-4fe2-97e2-124c65efb858
-- title:
--   Max-flow min-cut theorem
-- statement:
--   **(Bertsimas & Tsitsiklis, Theorem 7.10, p. 310, GOAL)**
--
--   - **(a)** If the Ford–Fulkerson algorithm terminates because no augmenting path can be found, then the current flow is optimal.
--   - **(b)** (Max-flow min-cut theorem) The value of the maximum flow is equal to the minimum cut capacity.
--
--   *Encoding:* (Part (a) is formalized by its exact mathematical content: a feasible flow admitting no augmenting path is optimal — precisely the Step-3 termination state, and all the book's proof uses. In part (b) both sides may simultaneously be $+\infty$; the book's proof (p. 311) treats the infinite case explicitly, and in the finite case the maximum is attained, with a minimum-capacity cut given by the labeled set $S$ at termination.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 7.10, p. 310

import Definitions.Def_LinearOptimization_AugmentingPath
import Definitions.Def_LinearOptimization_Cut


open Matrix
open scoped ENNReal

/-- **Bertsimas & Tsitsiklis, Theorem 7.10 (p. 310).** (a) A feasible flow of the maximum
flow problem admitting no augmenting path is optimal. (b) Max-flow
min-cut: the value of the maximum flow equals the minimum cut capacity
(in `EReal`; both sides may be `+∞`), and when finite the maximum is
attained by a feasible flow. -/

theorem LinearOptimization.max_flow_min_cut {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (u : Fin m → ℝ≥0∞) (s t : Fin n)
    (hst : s ≠ t) (hloop : HasNoSelfLoops arcs) (hupos : ∀ k, 0 < u k) :
    (∀ f, IsFeasibleMaxFlow arcs u s t f →
      (¬∃ steps, IsAugmentingPath arcs u s t f steps) →
      ∀ f', IsFeasibleMaxFlow arcs u s t f' →
        flowValue arcs s f' ≤ flowValue arcs s f) ∧
    maxFlowValue arcs u s t =
      ⨅ S ∈ {S : Finset (Fin n) | IsCut s t S},
        ((cutCapacity arcs u S : ℝ≥0∞) : EReal) ∧
    (maxFlowValue arcs u s t ≠ ⊤ →
      ∃ f, IsFeasibleMaxFlow arcs u s t f ∧
        ((flowValue arcs s f : ℝ) : EReal) = maxFlowValue arcs u s t) := by
  sorry
