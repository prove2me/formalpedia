-- Prove2me | Theorems.Thm_LinearOptimization_network_no_negative_cycle_optimal
-- name    : LinearOptimization.network_no_negative_cycle_optimal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-06T14:36:21.194941+00:00
-- url     : https://prove2.me/theorems/1f48be42-38a1-49bd-b4d2-4b2c7a9bf819
-- title:
--   Flow optimality iff no unsaturated negative-cost cycle
-- statement:
--   **(Bertsimas & Tsitsiklis, Theorem 7.6, p. 298)** A feasible flow $\mathbf{f}$ is optimal if and only if there is no unsaturated cycle with negative cost.
--
--   (Setting: the general capacitated minimum cost network flow problem of §7.2. A cycle $C$ with forward-arc set $F$ and backward-arc set $B$ is unsaturated under $\mathbf{f}$ if $f_{ij}<u_{ij}$ for all $(i,j)\in F$ and $f_{ij}>0$ for all $(i,j)\in B$ (pp. 293-294, equivalently $\delta(C)>0$ in Eq. (7.12)); its cost is
--
--   $$\mathbf{c}'\mathbf{h}^C=\sum_{(i,j)\in F}c_{ij}-\sum_{(i,j)\in B}c_{ij}.$$
--
--   'Optimal' = attains the minimum cost among feasible flows.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 7.6, p. 298

import Definitions.Def_LinearOptimization_NetworkFlowProblem


open Matrix
open scoped ENNReal

/-- **Bertsimas & Tsitsiklis, Theorem 7.6 (p. 298).** A feasible flow `f` of the (capacitated)
minimum cost network flow problem is optimal iff no cycle is both
unsaturated under `f` (`f_k < u_k` on forward arcs, `f_k > 0` on backward
arcs) and of negative cost `c'h^C < 0`. -/

theorem LinearOptimization.network_no_negative_cycle_optimal {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (hloop : HasNoSelfLoops arcs)
    (bsupply : Fin n → ℝ) (u : Fin m → ℝ≥0∞) (cost : Fin m → ℝ)
    (f : Fin m → ℝ) (hf : IsFeasibleFlow arcs bsupply u f) :
    (∀ f', IsFeasibleFlow arcs bsupply u f' → cost ⬝ᵥ f ≤ cost ⬝ᵥ f') ↔
      ¬∃ (v : Fin n) (steps : List (Fin m × Bool)),
        IsCycle arcs v steps ∧
        (∀ st ∈ steps, st.2 = true → ENNReal.ofReal (f st.1) < u st.1) ∧
        (∀ st ∈ steps, st.2 = false → 0 < f st.1) ∧
        cost ⬝ᵥ traversalVector steps < 0 := by
  sorry
