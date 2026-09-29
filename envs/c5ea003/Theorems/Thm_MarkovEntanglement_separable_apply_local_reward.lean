-- Prove2me | Theorems.Thm_MarkovEntanglement_separable_apply_local_reward
-- name    : MarkovEntanglement.separable_apply_local_reward
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T05:25:15.375003+00:00
-- url     : https://prove2.me/theorems/1d26d90a-d447-4efd-94c4-777383648e2b
-- title:
--   A separable transition acts on a local reward one agent at a time
-- statement:
--   ## Statement
--
--   **Lemma.** Let $P = \sum_{j=1}^{K} x_j\, P^{(j)}_1 \otimes \cdots \otimes P^{(j)}_N$ be
--   separable and let $r_i$ depend only on agent $i$'s coordinate. Then
--   $$\Bigl( \sum_{j} x_j\, P^{(j)}_1 \otimes \cdots \otimes P^{(j)}_N \Bigr)
--     \bigl( e^{\otimes (i-1)} \otimes r_i \otimes e^{\otimes (N-i)} \bigr)
--     \;=\; e^{\otimes (i-1)} \otimes \Bigl( \sum_j x_j P^{(j)}_i r_i \Bigr) \otimes e^{\otimes (N-i)} .$$
--
--   ## Notes
--
--   The computational engine behind exact value decomposition. Applying a separable transition
--   to a reward that involves only agent $i$ leaves every other coordinate untouched: the other
--   factors act on the all-ones vector $e$ and return it unchanged, because each $P^{(j)}_k$ is
--   a transition matrix and therefore row-stochastic.
--
--   Iterating this is what shows the Bellman recursion never mixes agents, so the $Q$-function
--   stays a sum of local terms. It is elementary but does the real work.
--
--   Search terms: tensor product of stochastic matrices, row-stochastic acts trivially on the
--   all-ones vector, Kronecker product Bellman recursion.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Lemma 6, p. 40

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem separable_apply_local_reward
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {K : ℕ} (x : Fin K → ℝ) (Pj : Fin K → ∀ i, Matrix (S i) (S i) ℝ)
    (hPj : ∀ k i, IsTransitionMatrix (Pj k i)) (hx : ∑ k, x k = 1)
    (i : Fin N) (r : S i → ℝ) (p : Joint S) :
    ∑ q : Joint S, (∑ k, x k • tensorProdN (Pj k)) p q * r (q i)
      = ∑ k, x k * ∑ t : S i, Pj k i (p i) t * r t := by
  sorry

end MarkovEntanglement
