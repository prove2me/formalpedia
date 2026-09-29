-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_two_state_gadget_reward_le_reference_plus_planted_plays
-- name    : BanditAlgorithm.jao_two_state_gadget_reward_le_reference_plus_planted_plays
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T17:32:03.433197+00:00
-- url     : https://prove2.me/theorems/62f109e7-91dd-4f96-a987-6d5c8b0aed87
-- title:
--   JAO equation (34): the reward collected in the planted gadget is at most $T - \mathbb{E}_{\mathrm{unif}}[N_p] + \varepsilon D' \mathbb{E}_a[N_\circ^*]$
-- statement:
--   Throughout, the MDP is the collapsed two-state gadget of JAO Figure 3, presented by its defining equations rather than through an auxiliary definition: state $0$ is $s_\circ$ with reward $0$, state $1$ is $s_p$ with reward $1$, the return probability is $p(s_\circ \mid s_p, b) = \delta$ for every action $b$, and the escape probability is $p(s_p \mid s_\circ, b) = \delta$ for every action other than the planted action $a$, for which it is $\delta + \varepsilon$. The gadget has diameter $D' = 1/\delta$. The reference MDP $M_0$ is the same gadget with no planting.
--
--   **Statement.** For every horizon $T$ and every policy $\pi$, writing $N_p$ for the number of rounds spent in $s_p$ (which, because the reward is the indicator of $s_p$, is exactly the total reward collected) and $N_\circ^*$ for the number of rounds in which the planted action $a$ is played in state $s_\circ$,
--   $$\mathbb{E}_a[N_p] \;\le\; T - \mathbb{E}_{\mathrm{unif}}[N_p] + \tfrac{\varepsilon}{\delta}\,\mathbb{E}_a[N_\circ^*].$$
--   Here $\mathbb{E}_a$ is the expectation under the planted gadget and $\mathbb{E}_{\mathrm{unif}}$ that under the reference gadget $M_0$, both run against the *same* policy $\pi$ from $s_\circ$, and $\tfrac{\varepsilon}{\delta} = \varepsilon D'$.
--
--   This is equation (34) of JAO (p. 1583), in the form in which the rest of the argument consumes it. The proof has three steps. First, a one-step conditioning identity: summing $\mathbb{P}_a[s_t = s_p]$ over $t$ and splitting on the previous state gives
--   $$\mathbb{E}_a[N_p] \;\le\; \delta\,\mathbb{E}_a[N_\circ - N_\circ^*] + (\delta+\varepsilon)\,\mathbb{E}_a[N_\circ^*] + (1-\delta)\,\mathbb{E}_a[N_p],$$
--   whence $\mathbb{E}_a[N_p] \le \mathbb{E}_a[N_\circ] + \varepsilon D' \mathbb{E}_a[N_\circ^*]$. Second, playing the planted action can only *reduce* the probability of remaining in $s_\circ$, so $\mathbb{E}_a[N_\circ] \le \mathbb{E}_{\mathrm{unif}}[N_\circ]$; this is a coupling between the two gadgets under the common policy. Third, $N_\circ + N_p = T$ identically, so $\mathbb{E}_{\mathrm{unif}}[N_\circ] = T - \mathbb{E}_{\mathrm{unif}}[N_p]$.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1583-1586): equations (34)-(37), Lemma 13 and the concluding computation. Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2 and its proof in the appendix.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_two_state_gadget_reward_le_reference_plus_planted_plays
    {m : ℕ} (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (a : Fin m) (M M₀ : FiniteMDP 2 m)
    (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ)
    (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0))
    (hr0' : ∀ b, M₀.r 0 b = 0) (hr1' : ∀ b, M₀.r 1 b = 1)
    (hP1' : ∀ b, (M₀.P 1 b 0 : ℝ) = δ) (hP0' : ∀ b, (M₀.P 0 b 1 : ℝ) = δ)
    (T : ℕ) (π : MDPPolicy 2 m) :
    (∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac 0) π T))
      ≤ (T : ℝ)
          - (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac 0) π T))
          + (ε / δ)
              * ∫ h, (mdpVisitCount h T 0 a : ℝ) ∂(mdpMeasure M (mdpStateDirac 0) π T) := by
  sorry
