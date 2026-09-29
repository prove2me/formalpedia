-- Prove2me | Theorems.Thm_MarkovEntanglement_agentwise_marginal_independence_implies_separable
-- name    : MarkovEntanglement.agentwise_marginal_independence_implies_separable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-09T16:04:05.564518+00:00
-- url     : https://prove2.me/theorems/6fc04784-9306-44ef-8121-289c072fd954
-- title:
--   Agent-wise marginal independence characterizes separable joint transitions
-- statement:
--   **Agent-wise marginal independence forces separability.**
--
--   Let $P$ be a transition matrix on the joint state-action space $\mathcal S=\prod_{i=1}^N S_i$ of $N$ agents. Suppose that for every agent $i$, summing $P$ over agent $i$'s *next* state leaves a quantity that no longer depends on agent $i$'s *current* state: for all $s,s'\in S_i$ and all joint state-action pairs $p,q$,
--
--   $$\sum_{t\in S_i} P\bigl((p_{-i},s),(q_{-i},t)\bigr) = \sum_{t\in S_i} P\bigl((p_{-i},s'),(q_{-i},t)\bigr).$$
--
--   Then $P$ is separable in the sense of Definition 10: it is a finite affine combination of $N$-fold tensor products of local transition matrices,
--   $$P=\sum_k x_k\, P_{k,1}\otimes\cdots\otimes P_{k,N},\qquad \sum_k x_k=1 .$$
--
--   ## Notes
--
--   The converse is immediate, so this is a characterization of separability: an agent is decoupled from the joint chain exactly when its own marginal dynamics are blind to its own state. In the tensor picture, writing $\Omega_m$ for the span of the $m\times m$ transition matrices (Lemma 3), the hypothesis says $P$ lies in $V\otimes\cdots\otimes\Omega_i\otimes\cdots\otimes V$ for each $i$, and the conclusion is that the intersection over $i$ is $\Omega_1\otimes\cdots\otimes\Omega_N$ — the $N$-fold tensor-intersection identity that the two-agent argument of Appendix D only needs for $N=2$.
-- source:
--   Chen and Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3: Definition 10 (N-agent separability) p. 20, Lemma 3 (span of transition matrices) p. 34, Lemma 4 p. 35; the N-fold tensor form of the linear-algebra step used for two agents in Appendix D, pp. 34-36

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem agentwise_marginal_independence_implies_separable
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (hmarg : ∀ (i : Fin N) (p p' q : Joint S), (∀ j, j ≠ i → p j = p' j) →
      ∑ t : S i, P p (Function.update q i t) = ∑ t : S i, P p' (Function.update q i t)) :
    IsSeparableN P := by
  sorry

end MarkovEntanglement
