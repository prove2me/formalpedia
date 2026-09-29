-- Prove2me | Theorems.Thm_MarkovEntanglement_two_agent_value_decomposition_implies_separable
-- name    : MarkovEntanglement.two_agent_value_decomposition_implies_separable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-07T18:09:51.696381+00:00
-- url     : https://prove2.me/theorems/bee48989-ee37-47d7-a973-ea6c61fa0d09
-- title:
--   Exact value decomposition by reward-local maps forces separability (two agents)
-- statement:
--   **Theorem 2 (Chen and Peng, arXiv:2506.02385v3, p. 12): exact value decomposition forces separability.**
--
--   Consider a two-agent MDP with joint transition $P^\pi_{AB}$, a policy $\pi$, and discount factor $\gamma \in (0,1)$. Suppose there exist **local functions** $Q_A : r_A \mapsto \mathbb{R}^{|S_A||A_A|}$ and $Q_B : r_B \mapsto \mathbb{R}^{|S_B||A_B|}$ such that for *every* pair of local rewards $r_A, r_B$ the global Q-value decomposes as
--   $$Q^\pi_{AB} = Q_A(r_A)\otimes e + e \otimes Q_B(r_B).$$
--   Then the two agents are separable. Combined with Theorem 1, Markov entanglement is a necessary and sufficient condition for exact value decomposition.
--
--   **Each $Q_i$ must be a function of its own reward alone.** The existential over the pair $(Q_A, Q_B)$ is quantified *outside* the rewards, so a single pair of maps must work for all reward profiles. If instead one only assumes that for each profile *some* additive decomposition exists — letting the witness depend on the whole profile — the statement fails. The paper's own Appendix E (p. 41) gives the witness: for $P = \tfrac14 ee^\top\otimes ee^\top + \delta(\varepsilon e^\top)\otimes(e\varepsilon^\top)$ with $e=(1,1)^\top$, $\varepsilon=(1,-1)^\top$, one computes
--   $$(I-\gamma P)^{-1}(r_A\otimes e + e\otimes r_B) = r_A\otimes e + r_B\otimes e + (h_A+h_B)(\gamma+\gamma^2/2)\,e\otimes e + 2\delta\gamma(\varepsilon^\top r_B)\,\varepsilon\otimes e,$$
--   which is additively decomposable for every $r_A, r_B$, while $P$ is entangled (its distance to the $9$-dimensional span of tensor products of transition matrices is $0.2$ at $\delta = 1/20$). The offending term $2\delta\gamma(\varepsilon^\top r_B)\varepsilon\otimes e$ is a function of agent $A$'s coordinate that depends on $r_B$ — precisely the dependence the hypothesis above forbids. The necessity argument also uses this: it compares $r_B = v$ with $r_B = -v$ and needs the *same* $Q_A(0)$ in both.
--
--   **Scope.** The statement is given for two agents, following the source; Appendix D's proof is written for two agents. Whether it generalizes to $N$ agents is not addressed here.
--
--   **Proof route.** By linearity the hypothesis forces, for each agent, the corresponding marginal of $(I-\gamma P)^{-1}$ to depend only on that agent's coordinate. For two agents this is exactly the criterion that a matrix lies in the span of tensor products of transition matrices, namely that for each agent $i$ the sum $\sum_{t_i} M(s,t)$ is independent of $s_i$. Since $(1-\gamma)(I-\gamma P)^{-1}$ has row sums one, it is then separable, and Lemma 4 transfers separability back to $P$.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Theorem 2, p. 12; full proof Appendix D, pp. 34-36; the counterexample to the weakened hypothesis is the paper's own Appendix E, p. 41

import Mathlib
import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem two_agent_value_decomposition_implies_separable
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hdec : ∃ (QA : (SA → ℝ) → (SA → ℝ)) (QB : (SB → ℝ) → (SB → ℝ)),
      ∀ (rA : SA → ℝ) (rB : SB → ℝ) (Q : SA × SB → ℝ),
        IsBellmanQ P (fun p => rA p.1 + rB p.2) γ Q →
          ∀ p : SA × SB, Q p = QA rA p.1 + QB rB p.2) :
    IsSeparable P := by
  sorry

end MarkovEntanglement
