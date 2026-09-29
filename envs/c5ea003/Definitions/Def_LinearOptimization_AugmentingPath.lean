-- Prove2me | Definitions.Def_LinearOptimization_AugmentingPath
-- name    : LinearOptimization_AugmentingPath
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-06T14:36:05.598611+00:00
-- url     : https://prove2.me/theorems/12d77786-cbd3-4300-8c91-0a80599fef53
-- title:
--   Augmenting path and the Ford–Fulkerson algorithm
-- statement:
--   **(Bertsimas & Tsitsiklis, Definition 7.2, p. 304, and the Ford–Fulkerson algorithm, p. 305)** Let $\mathbf{f}$ be a feasible flow vector. An *augmenting path* is a path from $s$ to $t$ such that $f_{ij}<u_{ij}$ for all forward arcs, and $f_{ij}>0$ for all backward arcs on the path. (Paths may traverse arcs in either direction, irrespective of the arc's orientation, §7.1; $F$ and $B$ denote the sets of forward and backward arcs of the path.)
--
--   The amount of flow pushed along an augmenting path $P$ can be no more than
--
--   $$\delta(P)=\min\{\min_{(i,j)\in F}(u_{ij}-f_{ij}),\ \min_{(i,j)\in B}f_{ij}\}$$
--
--   (Eq. (7.13)); if the path consists exclusively of forward arcs all of infinite capacity, $\delta(P)=\infty$.
--
--   The Ford–Fulkerson algorithm (p. 305):
--
--   1. start with a feasible flow $\mathbf{f}$;
--   2. search for an augmenting path;
--   3. if no augmenting path can be found, the algorithm terminates;
--   4. if an augmenting path $P$ is found, then
--      - **(a)** if $\delta(P)<\infty$, push $\delta(P)$ units of flow along $P$ and go to Step 2;
--      - **(b)** if $\delta(P)=\infty$, the algorithm terminates.
--
--   *Encoding:* Encoded as a predicate on sequences of feasible flows (admissible runs) covering every augmenting-path selection rule, not as a program.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 7.2, p. 304; Ford–Fulkerson algorithm box and Eq. (7.13), pp. 304-305

import Definitions.Def_LinearOptimization_MaxFlowProblem

/-!
Augmenting paths and the Ford–Fulkerson algorithm.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §7.5:

- **Definition 7.2 (p. 304).** Let `f` be a feasible flow vector. An
  *augmenting path* is a path from `s` to `t` such that `fᵢⱼ < uᵢⱼ` for
  all forward arcs and `fᵢⱼ > 0` for all backward arcs on the path.
  (Paths traverse arcs irrespective of orientation, §7.1; `F` and `B`
  are the forward- and backward-arc sets of the path.)
- **Eq. (7.13) (p. 305).** The amount of flow that can be pushed along an
  augmenting path `P` is at most
  `δ(P) = min{ min_{(i,j)∈F} (uᵢⱼ − fᵢⱼ), min_{(i,j)∈B} fᵢⱼ }`;
  if the path consists exclusively of forward arcs of infinite capacity,
  `δ(P) = ∞`. Pushing `δ` units along `P` increases the flow by `δ` on
  forward arcs and decreases it by `δ` on backward arcs (p. 304), i.e.
  `f' = f + δ·h^P`.
- **The Ford–Fulkerson algorithm (p. 305).** 1. start with a feasible
  flow `f`; 2. search for an augmenting path; 3. if none exists, the
  algorithm terminates; 4. if a path `P` is found: (a) if `δ(P) < ∞`,
  push `δ(P)` units along `P` and go to step 2; (b) if `δ(P) = ∞`, the
  algorithm terminates (the optimal cost is `+∞`).

Design (series convention, faithfulness guard 9 — algorithms are
predicates, not programs): one Ford–Fulkerson iteration is the step
predicate `IsFordFulkersonStep` (feasible current flow, some augmenting
path with finite `δ`, exact update `f' = f + δ·h^P`); admissible runs are
sequences of flows related by it, quantified over in the theorems — this
covers every augmenting-path selection rule. Termination statements are
"no infinite admissible run" (Theorem 7.8); the step-3 terminal state "no
augmenting path exists" appears directly in Theorem 7.10(a). `δ(P)` is
the `ℝ≥0∞` minimum of the per-step slacks (forward: `u_k − f_k`;
backward: `f_k`), the empty minimum being `⊤`. The labeling algorithm and
Theorem 7.9 (pp. 308–309) are proof devices for finding augmenting paths
— notes only, not items.
-/

open Matrix
open scoped ENNReal

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Definition 7.2 (p. 304).** An augmenting path for the flow `f`:
a path from the source `s` to the sink `t` with `f_k < u_k` on every
forward arc and `f_k > 0` on every backward arc. -/
def IsAugmentingPath {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (u : Fin m → ℝ≥0∞) (s t : Fin n) (f : Fin m → ℝ)
    (steps : List (Fin m × Bool)) : Prop :=
  IsPathFrom arcs s t steps ∧
  (∀ st ∈ steps, st.2 = true → ENNReal.ofReal (f st.1) < u st.1) ∧
  (∀ st ∈ steps, st.2 = false → 0 < f st.1)

/-- **Bertsimas & Tsitsiklis, Eq. (7.13) (p. 305).** The maximal amount `δ(P)` of flow that
can be pushed along the path `P`: the minimum over the steps of the
residual capacity `u_k − f_k` (forward steps) resp. the flow `f_k`
(backward steps), valued in `ℝ≥0∞` — `⊤` iff the path consists
exclusively of forward arcs of infinite capacity. -/
noncomputable def augmentingDelta {m : ℕ} (u : Fin m → ℝ≥0∞)
    (f : Fin m → ℝ) (steps : List (Fin m × Bool)) : ℝ≥0∞ :=
  (steps.map fun st =>
    if st.2 then u st.1 - ENNReal.ofReal (f st.1)
    else ENNReal.ofReal (f st.1)).foldr min ⊤

/-- **Bertsimas & Tsitsiklis, pp. 304–305 (Ford–Fulkerson iteration).** One step of the
Ford–Fulkerson algorithm from the feasible flow `f` to `f'`: some
augmenting path `P` with `δ(P) < ∞` is chosen and `δ(P)` units of flow
are pushed along it, `f' = f + δ(P)·h^P` (increase on forward arcs,
decrease on backward arcs). Admissible runs are sequences of flows
related by this predicate — every augmenting-path selection rule is
covered; the algorithm terminates at `f` when no augmenting path exists
(step 3) or when some augmenting path has `δ(P) = ∞` (step 4(b)). -/
def IsFordFulkersonStep {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (u : Fin m → ℝ≥0∞) (s t : Fin n) (f f' : Fin m → ℝ) : Prop :=
  IsFeasibleMaxFlow arcs u s t f ∧
  ∃ steps, IsAugmentingPath arcs u s t f steps ∧
    augmentingDelta u f steps ≠ ⊤ ∧
    f' = fun k =>
      f k + (augmentingDelta u f steps).toReal * traversalVector steps k

end LinearOptimization


