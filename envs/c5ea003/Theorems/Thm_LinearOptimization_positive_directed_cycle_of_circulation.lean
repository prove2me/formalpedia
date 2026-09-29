-- Prove2me | Theorems.Thm_LinearOptimization_positive_directed_cycle_of_circulation
-- name    : LinearOptimization.positive_directed_cycle_of_circulation
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-06T16:05:53.818767+00:00
-- url     : https://prove2.me/theorems/51b389bc-838a-48bf-a9b4-fc9784b78272
-- title:
--   A nonzero nonnegative circulation contains a positive directed cycle
-- statement:
--   Let $G=(\mathcal N,\mathcal A)$ be a finite directed network with no self-loops, and let $f\in\mathbb R^{\mathcal A}$ be a nonzero nonnegative circulation, so $Af=0$ for the node--arc incidence matrix $A$. Then there is a simple directed cycle $C$ entirely contained in the positive support of $f$:
--
--   $$
--   \exists C\qquad C\text{ is a simple directed cycle and }f_e>0\text{ for every }e\in C.
--   $$
--
--   This cycle-extraction lemma is the combinatorial step used when decomposing a nonnegative circulation into positive multiples of simple circulations.
--
--   **Formalization Note** The cycle is returned as a nonempty list of forward arc traversals; its internal vertices and arc indices are both duplicate-free.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, proof of Lemma 7.1, p. 298

import Definitions.Def_LinearOptimization_NetworkFlowProblem

open Matrix

theorem LinearOptimization.positive_directed_cycle_of_circulation
    {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (hloop : HasNoSelfLoops arcs) (f : Fin m → ℝ)
    (hnn : 0 ≤ f) (hcirc : IsCirculation arcs f) (hne : f ≠ 0) :
    ∃ (v : Fin n) (steps : List (Fin m × Bool)),
      IsCycle arcs v steps ∧
      (∀ st ∈ steps, st.2 = true) ∧
      ∀ st ∈ steps, 0 < f st.1 := by
  sorry
