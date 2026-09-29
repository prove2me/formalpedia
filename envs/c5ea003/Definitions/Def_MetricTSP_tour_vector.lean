-- Prove2me | Definitions.Def_MetricTSP_tour_vector
-- name    : MetricTSP_tour_vector
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-24T19:19:12.438482+00:00
-- url     : https://prove2.me/theorems/02f6b3ae-920a-4d95-93b3-1af7cb7f8e02
-- title:
--   The incidence vector of a Hamiltonian tour
-- statement:
--   The **incidence vector** of a Hamiltonian tour, the object that connects tours to the subtour-elimination (Held--Karp) linear program.
--
--   For an ordering $\pi$ of $n$ cities (a permutation of $\{0,\dots,n-1\}$), the tour visits $\pi(0), \pi(1), \dots, \pi(n-1)$ and returns to $\pi(0)$. For a pair of cities $u, v$:
--
--   1. `tourSteps` $\pi\,u\,v$ is the set of positions $i$ whose step of the tour --- from the city $\pi(i)$ to the next city $\pi(i+1)$ (cyclically) --- traverses the unordered pair $\{u, v\}$ in either direction;
--   2. `tourVec` $\pi\,u\,v$ is the number of such steps, as a real number.
--
--   For $n \ge 3$ the tour is a Hamiltonian cycle and no pair is traversed twice, so `tourVec` is the classical $0/1$ incidence vector: $x_{uv} = 1$ exactly when $u$ and $v$ are adjacent on the cycle. It is symmetric with zero diagonal, every city has degree $2$, and every nontrivial cut is crossed at least twice --- that is, it is a feasible point of the subtour-elimination relaxation, which is the validity half of the Held--Karp bound.
--
--   **Formalization Note.** `tourVec` is defined as the cardinality of `tourSteps`, so symmetry in $u, v$ holds definitionally, and nonnegativity is automatic; the $0/1$ property for $n \ge 3$ is a lemma, not part of the definition.
-- source:
--   G. Dantzig, R. Fulkerson, S. Johnson, Solution of a large-scale traveling-salesman problem, Operations Research 2 (1954) 393-410 (subtour-elimination constraints); M. Held, R. M. Karp, The traveling-salesman problem and minimum spanning trees, Operations Research 18 (1970) 1138-1162; D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press 2011, Section 11.2 (the incidence vector of a tour is feasible for the subtour LP).

import Mathlib

namespace MetricTSP

/-- The set of positions (steps) of the tour given by the ordering `π` that traverse
the unordered pair `{u, v}`: position `i` covers `{u, v}` when the step from the city
`π i` to the next city `π (finRotate n i)` goes from `u` to `v` or from `v` to `u`. -/
def tourSteps {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    (π i = u ∧ π (finRotate n i) = v) ∨ (π i = v ∧ π (finRotate n i) = u)

/-- The **incidence vector** of the Hamiltonian tour given by the ordering `π`:
the number of steps of the tour traversing the pair `{u, v}`, as a real number.
For `n ≥ 3` it takes values in `{0, 1}` and is the classical 0/1 incidence
vector of the Hamiltonian cycle visiting the cities in the order `π 0, π 1, …`. -/
noncomputable def tourVec {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) : ℝ :=
  ((tourSteps π u v).card : ℝ)

end MetricTSP


