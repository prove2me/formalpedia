-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_two_class_gadget_optimal_gain_ge
-- name    : BanditAlgorithm.jao_two_class_gadget_optimal_gain_ge
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-06T03:13:09.571528+00:00
-- url     : https://prove2.me/theorems/edceeab3-81b7-423e-9b91-8d344d463c78
-- title:
--   JAO Section 6: a two-class planted gadget has optimal average reward at least $\frac{\delta+\varepsilon}{2\delta+\varepsilon}$
-- statement:
--   **The two-class planted gadget.** The MDP is given by its defining equations rather than through an auxiliary definition. The data are a class map $\rho : S \to \{0,1\}$, an *escape* map $\mathrm{up}$, a *return* map $\mathrm{down}$ and a *navigation* map $\mathrm{nav}$, and $M$ satisfies: the reward is the class, $r(s,b) = \rho(s)$; from a class-$0$ state $s$ every action $b$ goes to the class-$1$ state $\mathrm{up}(s)$ with probability $\delta + \varepsilon\,[\,(s,b) = (s^*,b^*)\,]$ and to the class-$0$ state $\mathrm{nav}(s,b)$ otherwise; from a class-$1$ state $s$ every action goes to the class-$0$ state $\mathrm{down}(s)$ with probability $\delta$ and stays at $s$ otherwise. Every row is supported on two distinct states whose masses sum to $1$, so the transition function is pinned down completely. The reference MDP $M_0$ is the same shape with $\varepsilon = 0$. For $S = 2$ and $\rho = \mathrm{id}$ this is JAO Figure 3 with $D' = 1/\delta$; for $S > 2$ it is the composite of Figure 4, its class-$0$ states being the $s_\circ^{(i)}$.
--
--   The whole of JAO Section 6 is run at this level of generality, on the composite MDP itself rather than on the collapsed two-state MDP they pass to on p. 1583. That reduction is not available as an inequality between regrets: the simulating policy would have to be produced before the planting is chosen, and it sees neither which copy the composite is in nor which of the $A$ actions was played. Working with the class in place of the state avoids it, and no step of the argument is lost.
--
--   Throughout, the initial state $s_0$ is arbitrary and of either class.
--
--   **Statement.** For $0 < \delta \le \tfrac13$, $0 < \varepsilon \le \delta$, and a planted pair $(s^*,b^*)$ at a class-$0$ state which is a fixed point of the navigation map, $\mathrm{nav}(s^*,b^*) = s^*$, and satisfies $\mathrm{down}(\mathrm{up}(s^*)) = s^*$, the optimal gain satisfies $\rho^*(M) \ge \frac{\delta+\varepsilon}{2\delta+\varepsilon}$.
--
--   This is the quantity JAO compute on p. 1586 ("Calculating the stationary distribution, we find that the optimal average reward for the MDP $M'$ is $\frac{\delta+\varepsilon}{2\delta+\varepsilon}$"). Only the lower bound is needed: regret is $T\rho^* - \text{reward}$, so a large $\rho^*$ is what makes the bound strong.
--
--   **Proof.** The optimal gain is a supremum over initial states and over all policies, so one policy from one state suffices. Take the memoryless deterministic policy playing $b^*$ everywhere, started at $s^*$. The two hypotheses on the planted pair are exactly what confines the resulting chain to $\{s^*, \mathrm{up}(s^*)\}$: the navigation fixed point keeps a failed escape at $s^*$, and $\mathrm{down}(\mathrm{up}(s^*)) = s^*$ returns there. So the chain is the two-state gadget with escape probability $\delta+\varepsilon$ and return probability $\delta$, whose stationary mass on the class-$1$ state is $\frac{\delta+\varepsilon}{2\delta+\varepsilon}$. Writing $w(n)$ for the probability that round $n+1$ is in class $1$, one step gives $w(n+1) = (\delta+\varepsilon) + (1 - 2\delta - \varepsilon)w(n)$ with $w(0) = 0$; since the reward is the class indicator, the expected reward over $n$ rounds is the partial sum of $w$, so it is $\rho n$ minus a bounded geometric remainder, the Cesàro averages converge to $\rho$, and the $\limsup$ defining the gain equals it. Both suprema are then entered with `le_ciSup`, the boundedness coming from every reward lying in $[0,1]$.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1583-1586): equations (34)-(37), Lemma 13 and the optimal-gain computation. Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_two_class_gadget_optimal_gain_ge {S A : ℕ}
    (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
    (sStar : Fin S) (bStar : Fin A) (M : FiniteMDP S A)
    (hstar : ρ sStar = 0) (hfix : nav sStar bStar = sStar)
    (hud : down (up sStar) = sStar)
    (hrM : ∀ s b, M.r s b = ρ s)
    (hrow0M : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M.P s b (up s) : ℝ) = δ + (if (s, b) = (sStar, bStar) then ε else 0) ∧
        (M.P s b (nav s b) : ℝ) = 1 - δ - (if (s, b) = (sStar, bStar) then ε else 0))
    (hrow1M : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M.P s b (down s) : ℝ) = δ ∧ (M.P s b s : ℝ) = 1 - δ) :
    (δ + ε) / (2 * δ + ε) ≤ mdpOptimalGain M := by
  sorry
