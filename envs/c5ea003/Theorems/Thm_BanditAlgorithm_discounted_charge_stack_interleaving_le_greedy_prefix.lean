-- Prove2me | Theorems.Thm_BanditAlgorithm_discounted_charge_stack_interleaving_le_greedy_prefix
-- name    : BanditAlgorithm.discounted_charge_stack_interleaving_le_greedy_prefix
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T16:45:17.23331+00:00
-- url     : https://prove2.me/theorems/35d3c4e3-c18f-4a97-ac5e-7077c6980ced
-- title:
--   Finite discounted greedy charge-stack interleaving
-- statement:
--   Let $H_i(0),H_i(1),\ldots$ be a nonincreasing real-valued charge stack for each of $k$ arms. An interleaving chooses one stack at each round and receives its next unused charge. Suppose the interleaving $a^*$ is greedy through round $N-1$: at every $n<N$, its selected next charge is at least the currently available next charge of every arm. For any other interleaving $a$ and any discount factor $0\leq\alpha\leq1$,
--
--   $$
--   \sum_{n=0}^{N-1}\alpha^n H_{a_n}\!\left(T_{a_n}(n)\right)
--   \;\leq\;
--   \sum_{n=0}^{N-1}\alpha^n H_{a_n^*}\!\left(T^*_{a_n^*}(n)\right),
--   $$
--
--   where $T_i(n)$ is the number of entries already taken from stack $i$ before round $n$ under the relevant interleaving.
--
--   This finite-horizon greedy-interleaving inequality isolates the deterministic rearrangement step used in the Gittins-index proof and is reusable independently of the stochastic bandit coupling.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, §35.4, proof of Lemma 35.10, printed pp. 452–453 (free PDF pp. 460–461), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_GittinsChargeInterleaving

namespace BanditAlgorithm

theorem discounted_charge_stack_interleaving_le_greedy_prefix
    {k N : ℕ} {H : Fin k → ℕ → ℝ} {astar : ℕ → Fin k}
    (hH : ∀ i, Antitone (H i))
    (hastar : ∀ n, n < N → ∀ i,
      H i (stackPullCountBefore astar i n) ≤
        H (astar n) (stackPullCountBefore astar (astar n) n))
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (a : ℕ → Fin k) :
    (∑ n ∈ Finset.range N,
        α ^ n * chargeStackInterleaving H a n) ≤
      ∑ n ∈ Finset.range N,
        α ^ n * chargeStackInterleaving H astar n := by
  sorry

end BanditAlgorithm
