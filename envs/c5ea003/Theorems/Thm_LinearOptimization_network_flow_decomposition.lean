-- Prove2me | Theorems.Thm_LinearOptimization_network_flow_decomposition
-- name    : LinearOptimization.network_flow_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-06T14:36:13.344433+00:00
-- url     : https://prove2.me/theorems/46097692-3855-496c-b8fc-560c8c633f8a
-- title:
--   Flow decomposition theorem
-- statement:
--   **(Bertsimas & Tsitsiklis, Lemma 7.1, Flow decomposition theorem, p. 298)** Let $\mathbf{f}\ge 0$ be a nonzero circulation. Then, there exist simple circulations $\mathbf{f}^1,\dots,\mathbf{f}^k$, involving only forward arcs, and positive scalars $a_1,\dots,a_k$, such that
--
--   $$\mathbf{f}=\sum_{i=1}^k a_i\mathbf{f}^i.$$
--
--   Furthermore, if $\mathbf{f}$ is an integer vector, then each $a_i$ can be chosen to be an integer.
--
--   (A circulation satisfies $\mathbf{A}\mathbf{f}=0$; a simple circulation involving only forward arcs is the vector $\mathbf{h}^C$ of a directed cycle $C$, cf. §7.2 p. 278.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Lemma 7.1, p. 298

import Definitions.Def_LinearOptimization_NetworkFlowProblem


open Matrix

/-- **Bertsimas & Tsitsiklis, Lemma 7.1 (p. 298).** Flow decomposition: a nonzero circulation
`f ≥ 0` is a positive linear combination of simple circulations of
directed cycles (only forward arcs); if `f` is integer, the coefficients
can be chosen to be (positive) integers. -/

theorem LinearOptimization.network_flow_decomposition {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (hloop : HasNoSelfLoops arcs)
    (f : Fin m → ℝ) (hnn : 0 ≤ f) (hcirc : IsCirculation arcs f)
    (hne : f ≠ 0) :
    (∃ (k : ℕ) (cyc : Fin k → List (Fin m × Bool)) (a : Fin k → ℝ),
      (∀ i, ∃ v, IsCycle arcs v (cyc i)) ∧
      (∀ i, ∀ st ∈ cyc i, st.2 = true) ∧
      (∀ i, 0 < a i) ∧
      f = fun e => ∑ i, a i * traversalVector (cyc i) e) ∧
    ((∀ e, ∃ z : ℤ, f e = (z : ℝ)) →
      ∃ (k : ℕ) (cyc : Fin k → List (Fin m × Bool)) (a : Fin k → ℤ),
        (∀ i, ∃ v, IsCycle arcs v (cyc i)) ∧
        (∀ i, ∀ st ∈ cyc i, st.2 = true) ∧
        (∀ i, 0 < a i) ∧
        f = fun e => ∑ i, (a i : ℝ) * traversalVector (cyc i) e) := by
  sorry
