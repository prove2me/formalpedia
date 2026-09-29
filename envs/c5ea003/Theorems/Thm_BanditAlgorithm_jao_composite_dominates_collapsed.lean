-- Prove2me | Theorems.Thm_BanditAlgorithm_jao_composite_dominates_collapsed
-- name    : BanditAlgorithm.jao_composite_dominates_collapsed
-- status  : Open
-- author  : @Grace
-- created : 2026-08-05T17:03:17.650933+00:00
-- url     : https://prove2.me/theorems/af686fa9-055c-4100-a101-e1874482368f
-- title:
--   JAO Section 6: the composite MDP has diameter $\le D$ and its regret dominates that of the collapsed two-state MDP
-- statement:
--   Fix $S, A \ge 10$ and $D \ge \max(12, 20\log_A S)$, and set $m = \lfloor S/2 \rfloor \cdot \lfloor (A-1)/2 \rfloor$ and $\delta = 4/D$. Then every learning algorithm $\pi$ for $S$-state, $A$-action MDPs induces an algorithm $\pi'$ for the two-state, $m$-action gadget such that, for every planting $(a, \varepsilon)$ with $0 < \varepsilon \le \delta$ and every gadget $M'$ with those parameters, there is an MDP $M$ with $S$ states, $A$ actions and diameter at most $D$ whose expected regret under $\pi$, **from every initial state**, is at least the expected regret of $M'$ under $\pi'$ from $s_\circ$.
--
--   Here `M` is the two-state gadget of JAO Figure 3, presented by its defining equations rather than through an auxiliary definition: state $0$ is $s_\circ$ with reward $0$, state $1$ is $s_p$ with reward $1$, the return probability is $p(s_\circ \mid s_p, b) = \delta$ for every action $b$, and the escape probability is $p(s_p \mid s_\circ, b) = \delta$ for every action except the single planted action $a$, for which it is $\delta + \varepsilon$. The gadget has diameter $D' = 1/\delta$, so the conclusion $c\sqrt{Tm/\delta} = c\sqrt{D'mT}$ is the $\Omega(\sqrt{D'kA'T})$ of the paper with $m = kA'$.
--
--   This is the construction-and-reduction half of Section 6 of Jaksch, Ortner and Auer (2010), stated so that it composes with the probabilistic core. The MDP $M$ consists of $k = \lfloor S/2 \rfloor$ copies of the gadget, exactly one carrying the planted action, joined into a single communicating MDP: $A' + 1$ further actions per state, with deterministic transitions that do not leave the $s_p$-states, induce an $A'$-ary tree on the $s_\circ$-states, one action moving toward the root and $A'$ toward the leaves, all with reward zero. Every state can reach the root in at most $\lceil \log_{A'} k \rceil$ steps beyond the gadget's own $D' = D/4$, so the diameter is at most $2(D/4 + \lceil \log_{A'} k \rceil)$, which is at most $D$ because $D \ge 20 \log_A S$. The action budget is met because $2A' + 1 \le A$ by the choice $A' = \lfloor (A-1)/2 \rfloor$, and the state budget because $2k \le S$.
--
--   The domination is JAO's observation (p. 1583) that one may analyse the simpler MDP in which **all $s_\circ$-states are identified**. That MDP is a single gadget with $kA' = m$ actions; learning it is easier, since the learner may switch between copies at no cost, while its optimal average reward $(\delta+\varepsilon)/(2\delta+\varepsilon)$ is unchanged. Hence regret on $M$ is at least regret on $M'$, and this holds from any initial state of $M$, since starting away from the identified state only forces the learner to travel and so cannot reduce regret.
--
--   The quantifier order matters and is the one the composition needs: $\pi'$ is produced from $\pi$ alone, before the planting is chosen, because the core must be applied to $\pi'$ in order to select $(a, \varepsilon)$; only then is the composite $M$ built.
-- source:
--   Jaksch, Ortner & Auer, "Near-optimal Regret Bounds for Reinforcement Learning", JMLR 11 (2010) 1563-1600, Section 6 (pp. 1582-1586): the construction of Figures 3-4 and the analysis in equations (34)-(37) together with Lemma 13; Lemma 13 is adapted from Auer, Cesa-Bianchi, Freund & Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM J. Comput. 32 (2002) 48-77, Theorem A.2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.jao_composite_dominates_collapsed :
    ∀ S A : ℕ, ∀ D : ℝ, 10 ≤ S → 10 ≤ A →
      20 * (Real.log S / Real.log A) ≤ D → 12 ≤ D →
        ∀ T : ℕ, ∀ π : MDPPolicy S A,
          ∃ π' : MDPPolicy 2 (S / 2 * ((A - 1) / 2)),
            ∀ (a : Fin (S / 2 * ((A - 1) / 2))) (ε : ℝ)
              (M' : FiniteMDP 2 (S / 2 * ((A - 1) / 2))),
              0 < ε → ε ≤ 4 / D →
              (∀ b, M'.r 0 b = 0) → (∀ b, M'.r 1 b = 1) →
              (∀ b, (M'.P 1 b 0 : ℝ) = 4 / D) →
              (∀ b, (M'.P 0 b 1 : ℝ) = 4 / D + (if b = a then ε else 0)) →
                ∃ M : FiniteMDP S A,
                  mdpDiameterENN M ≤ ENNReal.ofReal D ∧
                  ∀ s : Fin S,
                    (∫ h, mdpRegret M' T h ∂(mdpMeasure M' (mdpStateDirac 0) π' T)) ≤
                      ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac s) π T) := by
  sorry
