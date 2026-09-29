-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_two_class_planted_plays_change_of_measure_two_valued
-- name    : BanditAlgorithm.jao_two_class_planted_plays_change_of_measure_two_valued
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-06T03:20:24.851221+00:00
-- url     : https://prove2.me/theorems/a749668c-a8fe-4efd-ab5e-f0b4e433f557
-- title:
--   JAO Lemma 13 for a two-class MDP: change of measure for the number of plays of the planted pair
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
--   $$\mathbb{E}_a\bigl[N_{(s^*,b^*)}\bigr] \;\le\; \mathbb{E}_{\mathrm{unif}}\bigl[N_{(s^*,b^*)}\bigr] + \frac{T}{2}\cdot\frac{\varepsilon}{\sqrt{\delta}}\cdot\sqrt{2\,\mathbb{E}_{\mathrm{unif}}\bigl[N_{(s^*,b^*)}\bigr]}.$$
--
--   This is equation (37) of JAO (p. 1584), obtained from their Lemma 13 applied to $f = N_{(s^*,b^*)}$, a function of the observed state-action history with values in $[0,T]$.
--
--   **Proof.** A divergence decomposition followed by Pinsker's inequality. The planted and reference MDPs differ in exactly one row of the transition function, namely $(s^*,b^*)$, so the relative entropy between the two trajectory laws under a common policy and a common initial distribution is $\mathbb{E}_{\mathrm{unif}}[N_{(s^*,b^*)}]$ times the relative entropy of the two rows. Both rows are two-point distributions on $\{\mathrm{up}(s^*), \mathrm{nav}(s^*,b^*)\}$ — this is why the gadget is set up with two-point rows — with masses $\delta$ and $\delta+\varepsilon$, so that relative entropy is the Bernoulli one $\mathrm{kl}(\delta \Vert \delta+\varepsilon)$, and $\delta + (\delta+\varepsilon) \le 3\delta \le 1$ gives $\mathrm{kl}(\delta \Vert \delta+\varepsilon) \le \varepsilon^2/\delta$. Pinsker then converts this into a bound on the difference of expectations of any $[0,1]$-valued function, applied to $N_{(s^*,b^*)}/T$.
--
--   JAO note that the observation in an MDP is the next state rather than the reward, which is harmless because the reward is a deterministic function of the state; the same remark applies here with the class in place of the state.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1583-1586): equations (34)-(37), Lemma 13 and the optimal-gain computation. Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_two_class_planted_plays_change_of_measure_two_valued {S A : ℕ}
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
    (∫ h, (mdpVisitCount h T sStar bStar : ℝ) ∂(mdpMeasure M (mdpStateDirac s₀) π T))
      ≤ (∫ h, (mdpVisitCount h T sStar bStar : ℝ) ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
        + (T : ℝ) / 2 * (ε / Real.sqrt δ)
            * Real.sqrt
                (2 * ∫ h, (mdpVisitCount h T sStar bStar : ℝ)
                        ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T)) := by
  sorry
