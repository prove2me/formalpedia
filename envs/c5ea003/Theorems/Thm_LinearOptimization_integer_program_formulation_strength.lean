-- Prove2me | Theorems.Thm_LinearOptimization_integer_program_formulation_strength
-- name    : LinearOptimization.integer_program_formulation_strength
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-09T15:59:56.79366+00:00
-- url     : https://prove2.me/theorems/3c12abe5-42ab-44c1-b64c-3fc8c51dd2f0
-- title:
--   Relative strength of spanning tree formulations: $P_{sub} \subseteq P_{cut}$
-- statement:
--   **(Theorem 10.1 — Bertsimas & Tsitsiklis, p. 467, Section 10.3.)** Let $G = (\mathcal{N}, \mathcal{E})$ be an undirected graph with $|\mathcal{N}| = n$. For $S \subseteq \mathcal{N}$ let $E(S) = \{\{i,j\} \in \mathcal{E} \mid i, j \in S\}$ and let $\delta(S) = \{\{i,j\} \in \mathcal{E} \mid i \in S,\ j \notin S\}$.
--
--   Let $P_{sub}$ be the feasible set of the linear programming relaxation of the subtour elimination formulation of the minimum spanning tree problem ($\sum_{e \in \mathcal{E}} x_e = n - 1$; $\sum_{e \in E(S)} x_e \le |S| - 1$ for all $S \subset \mathcal{N}$, $S \ne \emptyset, \mathcal{N}$; $0 \le x_e \le 1$), and let $P_{cut}$ be the feasible set of the linear programming relaxation of the cutset formulation ($\sum_{e \in \mathcal{E}} x_e = n - 1$; $\sum_{e \in \delta(S)} x_e \ge 1$ for all $S \subset \mathcal{N}$, $S \ne \emptyset, \mathcal{N}$; $0 \le x_e \le 1$).
--
--   The following properties hold:
--
--   - **(a)** We have $P_{sub} \subseteq P_{cut}$, and there exist examples for which the inclusion is strict.
--   - **(b)** The polyhedron $P_{cut}$ can have fractional extreme points.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 10.1, p. 467

import Mathlib.Analysis.Convex.Extreme
import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_MstRelaxations


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 10.1 (p. 467).** Formulation strength for the minimum
spanning tree problem: (a) `P_sub ⊆ P_cut` for every finite undirected
graph, and the inclusion can be strict; (b) `P_cut` can have fractional
extreme points. -/

theorem LinearOptimization.integer_program_formulation_strength :
    (∀ (n k : ℕ) (ends : Fin k → Fin n × Fin n),
      mstSubtourRelaxation ends ⊆ mstCutsetRelaxation ends) ∧
    (∃ (n k : ℕ) (ends : Fin k → Fin n × Fin n),
      ¬mstCutsetRelaxation ends ⊆ mstSubtourRelaxation ends) ∧
    (∃ (n k : ℕ) (ends : Fin k → Fin n × Fin n) (x : Fin k → ℝ),
      x ∈ Set.extremePoints ℝ (mstCutsetRelaxation ends) ∧
      ∃ e, ¬∃ z : ℤ, x e = (z : ℝ)) := by
  sorry
