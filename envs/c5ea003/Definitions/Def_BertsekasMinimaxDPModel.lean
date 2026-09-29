-- Prove2me | Definitions.Def_BertsekasMinimaxDPModel
-- name    : BertsekasMinimaxDPModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-04T16:50:34.223059+00:00
-- url     : https://prove2.me/theorems/aec8a0e3-577c-4d2d-b4ce-66d480676a44
-- title:
--   The minimax control model, worst-case costs, and the minimax DP recursion
-- statement:
--   This module fixes the **minimax** counterpart of the basic problem (Bertsekas, Vol. I, §1.6), in which the disturbance is not random but is chosen antagonistically.
--
--   The system, controls and costs are as in the stochastic model: $x_{k+1} = f_k(x_k,u_k,w_k)$ with $u_k \in U_k(x_k)$, stage costs $g_k$, terminal cost $g_N$, horizon $N$. What changes is the disturbance: at stage $k$, in state $x$ and under control $u$, it may be any element of a finite nonempty **membership set** $W_k(x,u)$, and it is chosen to maximize the resulting cost.
--
--   **Worst-case cost of a policy.** With $m$ stages remaining and $u = \mu_k(x)$ at stage $k = N-m-1$,
--
--   $$J_{\pi,m+1}(x) \;=\; \max_{w \in W_k(x,u)} \Bigl[g_k(x,u,w) + J_{\pi,m}\bigl(f_k(x,u,w)\bigr)\Bigr], \qquad J_{\pi,0} = g_N.$$
--
--   **The minimax DP recursion.** Equations (1.21)–(1.22) of the source read $J_N = g_N$ and
--
--   $$J_k(x) \;=\; \min_{u \in U_k(x)} \; \max_{w \in W_k(x,u)} \Bigl[g_k(x,u,w) + J_{k+1}\bigl(f_k(x,u,w)\bigr)\Bigr].$$
--
--   The minimax model is the natural home for reachability and target-tube problems (§4.6.2) and for the game-tree analysis of §6.3; it also shows which parts of the DP argument depend on averaging and which only on monotonicity.
--
--   **Formalization Note** No finiteness is assumed of the state, control or disturbance types; the constraint sets $U_k(x)$ and the membership sets $W_k(x,u)$ are finite and nonempty, so both extrema are attained. The maximization is over the disturbances admissible at the control actually played, and it sits inside the recursion — the adversary reacts stage by stage rather than committing to a disturbance sequence in advance. Stage indices use the same remaining-stages convention as the stochastic model.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 1.6

import Mathlib

/-- The finite-horizon minimax control model of Bertsekas, "Dynamic Programming
and Optimal Control", Vol. I, 3rd ed., Section 1.6: the disturbance `w` is
chosen antagonistically from a finite membership set `Wset k x u` rather than
according to a probability distribution. -/
structure BertsekasMinimaxDPModel (S C W : Type) where
  N : ℕ
  f : ℕ → S → C → W → S
  g : ℕ → S → C → W → ℝ
  gN : S → ℝ
  U : ℕ → S → Finset C
  hU : ∀ k x, (U k x).Nonempty
  Wset : ℕ → S → C → Finset W
  hW : ∀ k x u, (Wset k x u).Nonempty

/-- Worst-case cost-to-go of a policy `π` in the minimax control problem of
Section 1.6: the disturbances maximize the total cost subject to
`w_k ∈ Wset k x_k (π k x_k)`.  Backward recursion on remaining stages `m`. -/
noncomputable def BertsekasMinimaxPolicyCost {S C W : Type}
    (M : BertsekasMinimaxDPModel S C W) (π : ℕ → S → C) : ℕ → S → ℝ
  | 0, x => M.gN x
  | m + 1, x =>
      let k := M.N - (m + 1)
      let u := π k x
      (M.Wset k x u).sup' (M.hW k x u) fun w =>
        M.g k x u w + BertsekasMinimaxPolicyCost M π m (M.f k x u w)

/-- The minimax dynamic programming algorithm of Section 1.6 (Eqs. (1.21)-(1.22)):
backward recursion `J_k(x) = min_{u ∈ U k x} max_{w ∈ Wset k x u}
[g_k(x,u,w) + J_{k+1}(f_k(x,u,w))]`, indexed by remaining stages `m`. -/
noncomputable def BertsekasMinimaxValue {S C W : Type}
    (M : BertsekasMinimaxDPModel S C W) : ℕ → S → ℝ
  | 0, x => M.gN x
  | m + 1, x =>
      let k := M.N - (m + 1)
      (M.U k x).inf' (M.hU k x) fun u =>
        (M.Wset k x u).sup' (M.hW k x u) fun w =>
          M.g k x u w + BertsekasMinimaxValue M m (M.f k x u w)


