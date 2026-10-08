-- Prove2me | Theorems.Thm_WorstCaseEq_Identical_opt_ge_max
-- name    : WorstCaseEq.Identical.opt_ge_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:57.804981+00:00
-- url     : https://prove2.me/theorems/054cb478-b1ae-4fef-9525-a1836cdf5658
-- title:
--   §2, PDF p. 4 — opt ≥ max{w_i, Σ_i w_i/m}
-- statement:
--   Let $n$ agents with nonnegative traffics $w_1,\dots,w_n$ be assigned to $m\ge1$ identical links, and let $\mathrm{opt}$ be the least possible maximum link load over all assignments of agents to links. Then
--   $$
--   \mathrm{opt}\ \ge\ \max\Big\{w_i,\ \frac{1}{m}\sum_{k}w_k\Big\}\qquad\text{for every agent } i .
--   $$
--
--   These are the two elementary lower bounds on the optimum that the paper uses to bound the price of anarchy: some link carries agent $i$, and the busiest link carries at least the average load. For any mixed profile the expected traffics satisfy $\sum_j M^j=\sum_i w_i$, so the average load is also $\sum_j M^j/m$, which is how the page writes it.
--
--   **Formalization Note** The paper states the first bound for $w_1$ under the ordering $w_1\ge w_2\ge\dots\ge w_n$; the statement here gives it for every agent and assumes no ordering. Nonnegative traffics suffice.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 4, last paragraph of §2

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

namespace WorstCaseEq.Identical

/-- PDF p. 4: the social optimum is at least the traffic of every single agent and at least the average
load `∑_i w_i / m`. -/
theorem opt_ge_max {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∀ i, w i ≤ opt m w) ∧ (∑ i, w i) / m ≤ opt m w := by sorry

end WorstCaseEq.Identical
