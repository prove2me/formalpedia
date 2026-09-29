-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_phase_regret_telescope
-- name    : BanditAlgorithm.mdp_phase_regret_telescope
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T04:02:03.479749+00:00
-- url     : https://prove2.me/theorems/0ef481fd-42d7-4df8-a85e-ea55c476bad6
-- title:
--   Telescoping the per-phase regret of an optimistic algorithm
-- statement:
--   Let $\rho \in \mathbb{R}$ and $r, V, W, W^{k} : \mathbb{N} \to \mathbb{R}$ satisfy
--
--   $$\rho = r_t - V_t + W^{k}_t \qquad (t < N).$$
--
--   Then
--
--   $$\sum_{t<N} (\rho - r_t) \;=\; \big(V_N - V_0\big) \;+\; \sum_{t<N}\big(W_t - V_{t+1}\big) \;+\; \sum_{t<N}\big(W^{k}_t - W_t\big).$$
--
--   This is the rearrangement performed in Step 2 of the proof of the UCRL2 regret bound (Lattimore and Szepesvári, Theorem 38.6, Eq. 38.18–38.20 and the display following them). Inside the $k$-th phase the optimistic value function $v_k$ and gain $\rho_k$ satisfy the Bellman optimality equation along the realised trajectory,
--
--   $$\rho_k = r_{A_t}(S_t) - v_k(S_t) + \langle P_{k,A_t}(S_t), v_k\rangle,$$
--
--   which is the hypothesis with $V_t = v_k(S_t)$, $W^{k}_t = \langle P_{k,A_t}(S_t), v_k\rangle$ the optimistic one-step value, and $W_t = \langle P_{A_t}(S_t), v_k\rangle$ the same quantity under the *true* kernel. The conclusion splits the phase regret $\tilde R_k = \sum_{t \in E_k}(\rho_k - r_{A_t}(S_t))$ into the three pieces the analysis treats separately:
--
--   * the boundary term $v_k(S_{\tau_{k+1}}) - v_k(S_{\tau_k})$, bounded by $\mathrm{span}(v_k) \le D$ on the event that the confidence sets hold;
--   * the sum of martingale differences $\langle P_{A_t}(S_t), v_k\rangle - v_k(S_{t+1})$, whose terms are exactly $\mathbb{E}_t[v_k(S_{t+1})] - v_k(S_{t+1})$ and which is controlled by Hoeffding–Azuma;
--   * the estimation error $\langle P_{k,A_t}(S_t) - P_{A_t}(S_t), v_k\rangle$, bounded by Hölder's inequality against the $\ell^1$ radius of the confidence set.
--
--   The identity itself is pure algebra: substituting the hypothesis turns each summand into $(V_{t+1} - V_t) + (W_t - V_{t+1}) + (W^{k}_t - W_t)$, and the first block telescopes.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Step 2 of the proof of Theorem 38.6, Eq. (38.18)-(38.20); Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 4.3.

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

theorem BanditAlgorithm.mdp_phase_regret_telescope
    (N : ℕ) (ρ : ℝ) (rr V W Wk : ℕ → ℝ)
    (hbell : ∀ t < N, ρ = rr t - V t + Wk t) :
    ∑ t ∈ Finset.range N, (ρ - rr t)
      = (V N - V 0) + ∑ t ∈ Finset.range N, (W t - V (t + 1))
        + ∑ t ∈ Finset.range N, (Wk t - W t) := by
  sorry
