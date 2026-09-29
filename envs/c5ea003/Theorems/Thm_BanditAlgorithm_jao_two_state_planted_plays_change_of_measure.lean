-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_two_state_planted_plays_change_of_measure
-- name    : BanditAlgorithm.jao_two_state_planted_plays_change_of_measure
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-05T17:32:31.342491+00:00
-- url     : https://prove2.me/theorems/f7b6d9ae-dde7-4999-9070-31330c0be57e
-- title:
--   JAO Lemma 13: change of measure for the number of plays of the planted action
-- statement:
--   Throughout, the MDP is the collapsed two-state gadget of JAO Figure 3, presented by its defining equations rather than through an auxiliary definition: state $0$ is $s_\circ$ with reward $0$, state $1$ is $s_p$ with reward $1$, the return probability is $p(s_\circ \mid s_p, b) = \delta$ for every action $b$, and the escape probability is $p(s_p \mid s_\circ, b) = \delta$ for every action other than the planted action $a$, for which it is $\delta + \varepsilon$. The gadget has diameter $D' = 1/\delta$. The reference MDP $M_0$ is the same gadget with no planting.
--
--   **Statement.** For $0 < \varepsilon \le \delta \le \tfrac13$, every horizon $T$ and every policy $\pi$,
--   $$\mathbb{E}_a[N_\circ^*] \;\le\; \mathbb{E}_{\mathrm{unif}}[N_\circ^*] + \frac{T}{2}\cdot\frac{\varepsilon}{\sqrt{\delta}}\cdot\sqrt{2\,\mathbb{E}_{\mathrm{unif}}[N_\circ^*]},$$
--   where $N_\circ^*$ counts the rounds in which the planted action $a$ is played in state $s_\circ$.
--
--   This is equation (37) of JAO (p. 1584), obtained from their Lemma 13 applied to $f = N_\circ^*$, a function of the observed state-action history taking values in $[0, T]$. Lemma 13 itself states that for $f$ with values in $[0, B]$, $0 \le \delta \le \tfrac12$ and $0 \le \varepsilon \le 1 - 2\delta$,
--   $$\mathbb{E}_a[f] \;\le\; \mathbb{E}_{\mathrm{unif}}[f] + \frac{B}{2}\cdot\frac{\varepsilon}{\sqrt{\delta}}\sqrt{2\,\mathbb{E}_{\mathrm{unif}}[N_\circ^*]};$$
--   the hypothesis $\varepsilon \le \delta \le \tfrac13$ of the present statement gives $\varepsilon \le \tfrac13 \le 1 - 2\delta$, so the lemma applies.
--
--   The proof is a divergence decomposition followed by Pinsker's inequality. The planted and reference gadgets differ in exactly one row of the transition function, namely $(s_\circ, a)$, so the relative entropy between the two trajectory laws under a common policy is $\mathbb{E}_{\mathrm{unif}}[N_\circ^*]$ times the relative entropy $\mathrm{kl}(\delta + \varepsilon \,\|\, \delta) \le \frac{\varepsilon^2}{\delta(1-\delta)}$ of the two rows; Pinsker's inequality then converts this into a bound on the difference of expectations of any $[0,B]$-valued function. JAO note that the observation in an MDP is the next state rather than the reward, which is harmless here because the reward is a deterministic function of the state, so $N_\circ^*$ is a function of the state-action sequence and the argument of Auer et al. goes through verbatim.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1583-1586): equations (34)-(37), Lemma 13 and the concluding computation. Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2 and its proof in the appendix.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_two_state_planted_plays_change_of_measure
    {m : ℕ} (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (a : Fin m) (M M₀ : FiniteMDP 2 m)
    (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ)
    (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0))
    (hr0' : ∀ b, M₀.r 0 b = 0) (hr1' : ∀ b, M₀.r 1 b = 1)
    (hP1' : ∀ b, (M₀.P 1 b 0 : ℝ) = δ) (hP0' : ∀ b, (M₀.P 0 b 1 : ℝ) = δ)
    (T : ℕ) (π : MDPPolicy 2 m) :
    (∫ h, (mdpVisitCount h T 0 a : ℝ) ∂(mdpMeasure M (mdpStateDirac 0) π T))
      ≤ (∫ h, (mdpVisitCount h T 0 a : ℝ) ∂(mdpMeasure M₀ (mdpStateDirac 0) π T))
        + (T : ℝ) / 2 * (ε / Real.sqrt δ)
            * Real.sqrt
                (2 * ∫ h, (mdpVisitCount h T 0 a : ℝ)
                        ∂(mdpMeasure M₀ (mdpStateDirac 0) π T)) := by
  sorry
