-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_two_class_reward_le_reference_plus_planted_plays_two_valued
-- name    : BanditAlgorithm.jao_two_class_reward_le_reference_plus_planted_plays_two_valued
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-06T03:19:58.047183+00:00
-- url     : https://prove2.me/theorems/b05b970a-386d-42e7-b3a8-35db6e69a5f9
-- title:
--   JAO equation (34) for a two-class MDP: the reward collected under a planting exceeds the reference reward by at most $\frac{\varepsilon}{2\delta}$ times the plays of the planted pair
-- statement:
--   **The two-class planted gadget.** The MDP is given by its defining equations rather than through an auxiliary definition. The data are a class map $\rho : S \to \{0,1\}$, an *escape* map $\mathrm{up}$, a *return* map $\mathrm{down}$ and a *navigation* map $\mathrm{nav}$, and $M$ satisfies: the reward is the class, $r(s,b) = \rho(s)$; from a class-$0$ state $s$ every action $b$ goes to the class-$1$ state $\mathrm{up}(s)$ with probability $\delta + \varepsilon\,[\,(s,b) = (s^*,b^*)\,]$ and to the class-$0$ state $\mathrm{nav}(s,b)$ otherwise; from a class-$1$ state $s$ every action goes to the class-$0$ state $\mathrm{down}(s)$ with probability $\delta$ and stays at $s$ otherwise. Every row is supported on two distinct states whose masses sum to $1$, so the transition function is pinned down completely. The reference MDP $M_0$ is the same shape with $\varepsilon = 0$. For $S = 2$ and $\rho = \mathrm{id}$ this is JAO Figure 3 with $D' = 1/\delta$; for $S > 2$ it is the composite of Figure 4, its class-$0$ states being the $s_\circ^{(i)}$.
--
--   The whole of JAO Section 6 is run at this level of generality, on the composite MDP itself rather than on the collapsed two-state MDP they pass to on p. 1583. That reduction is not available as an inequality between regrets: the simulating policy would have to be produced before the planting is chosen, and it sees neither which copy the composite is in nor which of the $A$ actions was played. Working with the class in place of the state avoids it, and no step of the argument is lost.
--
--   Throughout, the initial state $s_0$ is arbitrary and of either class.
--
--   **On the two-valuedness hypothesis.** The statement carries $\forall s,\ \rho(s) \in \{0,1\}$ explicitly. It is not decoration: the row equations above only constrain states of class $0$ and of class $1$, so without it a state of neither class has a completely unconstrained transition row and an arbitrarily large reward, and the conclusion fails outright from such an initial state. An earlier version of this node omitted it and has been deprecated.
--
--   **Statement.** For $0 < \varepsilon \le \delta \le \tfrac13$, every horizon $T$, every policy $\pi$ and every initial state $s_0$,
--   $$\mathbb{E}_{a}\bigl[\text{reward}\bigr] \;\le\; \mathbb{E}_{\mathrm{unif}}\bigl[\text{reward}\bigr] + \frac{\varepsilon}{2\delta}\,\mathbb{E}_{a}\bigl[N_{(s^*,b^*)}\bigr],$$
--   where $\mathbb{E}_a$ is the expectation under the planted MDP and $\mathbb{E}_{\mathrm{unif}}$ that under the reference MDP, both run against the *same* policy from the *same* initial state, and $N_{(s^*,b^*)}$ counts the rounds in which the planted pair is played.
--
--   This is equation (34) of JAO (p. 1583) in the form the rest of the argument consumes, but obtained by a different and shorter route. Write $W(n)$ for the probability that the state of round $n+1$ has class $1$. Since the reward is the class indicator, the total expected reward is $\sum_{n<T} W(n)$. Conditioning on a single step and using that the escape probability is $\delta$ off the planted pair and $\delta + \varepsilon$ on it, while the return probability is $\delta$ everywhere,
--   $$W(n+1) = \delta + (1-2\delta)W(n) + \varepsilon\,Q(n),$$
--   with $Q(n)$ the probability that round $n+1$ plays the planted pair. The reference obeys the same recursion with $Q \equiv 0$ and the same initial value $W_0(0) = \rho(s_0)$, so the difference $d(n) = W(n) - W_0(n)$ satisfies $d(0) = 0$ and $d(n+1) = (1-2\delta)d(n) + \varepsilon Q(n)$. Summing that over $n < T$ **telescopes**, because $\sum_{n<T} d(n+1) = \sum_{n<T} d(n) + d(T) - d(0)$, and gives
--   $$2\delta \sum_{n<T} d(n) \;=\; \varepsilon \sum_{n<T} Q(n) - d(T) \;\le\; \varepsilon\,\mathbb{E}_a[N_{(s^*,b^*)}],$$
--   using $d(T) \ge 0$, which follows from the recursion by induction. JAO instead bound $\mathbb{E}_a[N_\circ] \le \mathbb{E}_{\mathrm{unif}}[N_\circ]$ by a stochastic-domination coupling between the two MDPs; the telescoping identity removes that step entirely, and it is also what makes the statement work from an arbitrary initial state, since the two recursions start from the same value whatever $\rho(s_0)$ is.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1583-1586): equations (34)-(37), Lemma 13 and the optimal-gain computation. Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_two_class_reward_le_reference_plus_planted_plays_two_valued {S A : ℕ}
    (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
    (hρ01 : ∀ s, ρ s = 0 ∨ ρ s = 1)
    (sStar : Fin S) (bStar : Fin A) (M M₀ : FiniteMDP S A)
    (hstar : ρ sStar = 0)
    (hrM : ∀ s b, M.r s b = ρ s)
    (hrow0M : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M.P s b (up s) : ℝ) = δ + (if (s, b) = (sStar, bStar) then ε else 0) ∧
        (M.P s b (nav s b) : ℝ) = 1 - δ - (if (s, b) = (sStar, bStar) then ε else 0))
    (hrow1M : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M.P s b (down s) : ℝ) = δ ∧ (M.P s b s : ℝ) = 1 - δ)
    (hrM₀ : ∀ s b, M₀.r s b = ρ s)
    (hrow0M₀ : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M₀.P s b (up s) : ℝ) = δ ∧
        (M₀.P s b (nav s b) : ℝ) = 1 - δ)
    (hrow1M₀ : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M₀.P s b (down s) : ℝ) = δ ∧ (M₀.P s b s : ℝ) = 1 - δ)
    (T : ℕ) (π : MDPPolicy S A) (s₀ : Fin S) :
    (∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac s₀) π T))
      ≤ (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
        + (ε / (2 * δ))
            * ∫ h, (mdpVisitCount h T sStar bStar : ℝ)
                ∂(mdpMeasure M (mdpStateDirac s₀) π T) := by
  sorry
