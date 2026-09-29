-- Prove2me | Theorems.Thm_LinearOptimization_traversalVector_isCirculation_of_isCycle
-- name    : LinearOptimization.traversalVector_isCirculation_of_isCycle
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-06T15:57:49.282712+00:00
-- url     : https://prove2.me/theorems/af5b99a0-efc8-4867-9921-8f9abf5dc715
-- title:
--   A simple-cycle traversal vector is a circulation
-- statement:
--   Let $G=(\mathcal N,\mathcal A)$ be a finite directed network with node--arc incidence matrix $A$. For a simple cycle $C$, let $h^C$ be its signed traversal vector: a forward traversal contributes $+1$ on its arc, a backward traversal contributes $-1$, and unused arcs contribute $0$. Then
--
--   $$
--   A h^C = 0.
--   $$
--
--   Thus every simple-cycle traversal vector is a circulation. This is the structural fact that makes cycle vectors reusable as the elementary summands in the flow-decomposition theorem.
--
--   **Formalization Note** A cycle is represented by a nonempty list of directed arc steps with no repeated internal vertex or arc index; the conclusion uses the platform definitions `traversalVector` and `IsCirculation`.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §7.2, p. 278 (definition of the simple circulation h^C); used in the proof of Lemma 7.1, p. 298

import Definitions.Def_LinearOptimization_NetworkFlowProblem

open Matrix

theorem LinearOptimization.traversalVector_isCirculation_of_isCycle
    {n m : ℕ} (arcs : Fin m → Fin n × Fin n) {v : Fin n}
    {steps : List (Fin m × Bool)} (hcyc : IsCycle arcs v steps) :
    IsCirculation arcs (traversalVector steps) := by
  sorry
