-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_two_state_gadget_optimal_gain_ge
-- name    : BanditAlgorithm.jao_two_state_gadget_optimal_gain_ge
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T17:31:49.695794+00:00
-- url     : https://prove2.me/theorems/81f67ac2-4646-4505-87b0-549806e4dd12
-- title:
--   JAO Section 6: the planted two-state gadget has optimal average reward at least $\frac{\delta+\varepsilon}{2\delta+\varepsilon}$
-- statement:
--   Throughout, the MDP is the collapsed two-state gadget of JAO Figure 3, presented by its defining equations rather than through an auxiliary definition: state $0$ is $s_\circ$ with reward $0$, state $1$ is $s_p$ with reward $1$, the return probability is $p(s_\circ \mid s_p, b) = \delta$ for every action $b$, and the escape probability is $p(s_p \mid s_\circ, b) = \delta$ for every action other than the planted action $a$, for which it is $\delta + \varepsilon$. The gadget has diameter $D' = 1/\delta$. The reference MDP $M_0$ is the same gadget with no planting.
--
--   **Statement.** For $0 < \delta \le \tfrac13$ and $0 < \varepsilon \le \delta$, the optimal gain of the planted gadget satisfies $\rho^*(M) \ge \frac{\delta + \varepsilon}{2\delta + \varepsilon}$.
--
--   This is the quantity JAO obtain on p. 1586 ("Calculating the stationary distribution, we find that the optimal average reward for the MDP $M'$ is $\frac{\delta+\varepsilon}{2\delta+\varepsilon}$"). Only the lower bound is stated here, because that is the direction a regret lower bound needs: regret is $T\rho^* - \text{reward}$, so a *large* $\rho^*$ is what makes the bound strong, and stating an inequality avoids having to prove that no policy does better.
--
--   **Proof.** The optimal gain is a supremum over initial states and over all policies, so it suffices to exhibit one policy from one state. Take the memoryless deterministic policy that plays the planted action $a$ in every state. It induces the two-state Markov chain with escape probability $\delta + \varepsilon$ out of $s_\circ$ and return probability $\delta$ out of $s_p$; since $\delta + \varepsilon \le 2\delta \le \tfrac23$, the chain is irreducible and aperiodic with stationary mass $\frac{\delta+\varepsilon}{2\delta+\varepsilon}$ on $s_p$. Because the reward is the indicator of $s_p$, the expected reward at step $t$ started from $s_\circ$ equals $\frac{\delta+\varepsilon}{2\delta+\varepsilon}\bigl(1 - \lambda^{t-1}\bigr)$ with $\lambda = 1 - 2\delta - \varepsilon \in [0,1)$, so the Cesàro averages converge to $\frac{\delta+\varepsilon}{2\delta+\varepsilon}$ from below and the $\limsup$ defining the gain equals it.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1583-1586): equations (34)-(37), Lemma 13 and the concluding computation. Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2 and its proof in the appendix.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_two_state_gadget_optimal_gain_ge
    {m : ℕ} (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (a : Fin m) (M : FiniteMDP 2 m)
    (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ)
    (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0)) :
    (δ + ε) / (2 * δ + ε) ≤ mdpOptimalGain M := by
  sorry
