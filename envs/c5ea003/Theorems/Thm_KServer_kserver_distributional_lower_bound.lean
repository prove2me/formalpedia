-- Prove2me | Theorems.Thm_KServer_kserver_distributional_lower_bound
-- name    : KServer.kserver_distributional_lower_bound
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-07T23:58:48.252346+00:00
-- url     : https://prove2.me/theorems/7abc7198-cf0f-4ec7-bb57-0c3eb4d78966
-- title:
--   A hard distribution for $k$ servers on $k+1$ points, with ratio $\Omega(\log^2 k)$
-- statement:
--   **The $k$-server lower bound of Bubeck--Coester--Rabani in its distributional form, stated directly for the $k$-server problem.**
--
--   There are a constant $c>0$ and a threshold $k_0$ such that for every $k\ge k_0$ there is a metric on the $(k+1)$-point space with the following property. For every initial configuration $C_0$ and every target $N$, there is a finitely supported distribution $(p_j)$ over request sequences $(\sigma_j)$ such that
--
--   * the expected offline optimum is at least $N$:
--   $$\sum_j p_j\,\mathrm{OPT}(C_0,\sigma_j)\;\ge\;N,$$
--   * and every deterministic online algorithm $A$ started at $C_0$ pays at least $c\log^2k$ times it:
--   $$c\log^2 k\,\sum_j p_j\,\mathrm{OPT}(C_0,\sigma_j)\;\le\;\sum_j p_j\,\mathrm{cost}_A(\sigma_j).$$
--
--   **Role.** This is the hard-distribution half of the refutation of the randomized $k$-server conjecture, and it implies the mission's milestone `KServer.randomized_lower_bound` through Yao's principle alone. Given a randomized algorithm that is $\rho$-competitive from $C_0$ with additive constant $a$, averaging produces a deterministic algorithm in its support whose cost on the distribution is at most $\rho$ times the expected optimum plus $a$, so
--   $$c\log^2k\;\Bigl(\sum_j p_j\,\mathrm{OPT}\Bigr)\;\le\;\rho\Bigl(\sum_j p_j\,\mathrm{OPT}\Bigr)+a+\varepsilon .$$
--   If $\rho$ were below $c\log^2k$ this would cap the expected optimum by a quantity depending only on $A$, and the freedom to demand an expected optimum above any $N$ contradicts it. The parameter $N$ is exactly what defeats the additive constant, and it is why the statement quantifies over $N$ rather than fixing one distribution.
--
--   **Why state it this way.** The milestone is already reduced, through the folklore equivalence between $k$-server on $k+1$ points and small set chasing, to a distributional bound for the evader problem. That route passes through several translation steps, two of which have already needed repair on this platform. The present statement is an independent route to the same milestone: it stays on the $k$-server side throughout, so the only bridge it needs is Yao averaging, which is proved (`KServer.randomized_yao_averaging`). Its content is the construction itself, not the translation, and a proof of it closes the milestone without depending on the evader formulation.
--
--   **Formalization notes.** The distribution is finitely supported, given as weights $p:\mathrm{Fin}\,n\to\mathbb R$ summing to one, which is the form Yao averaging consumes. The algorithms quantified over are the deterministic online algorithms of the mission's model, required to start at $C_0$. The lower bound is stated multiplicatively against the expected optimum rather than as a ratio, so no positivity of the optimum has to be assumed.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753, Theorem 11 and Definition 2 (the distributional lower bound on the randomized competitive ratio), transported from small set chasing to the k-server problem on k+1 points via Proposition 8.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem kserver_distributional_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ m : MetricSpace (Fin (k + 1)),
        ∀ (C₀ : Config k (Fin (k + 1))) (N : ℝ),
          ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → List (Fin (k + 1))),
            (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
            N ≤ ∑ j, p j * @offlineCost k (Fin (k + 1)) m C₀ (σ j) ∧
            ∀ A : @OnlineAlgorithm k (Fin (k + 1)) m,
              @OnlineAlgorithm.conf k (Fin (k + 1)) m A [] = C₀ →
              c * Real.log k ^ 2 * (∑ j, p j * @offlineCost k (Fin (k + 1)) m C₀ (σ j))
                ≤ ∑ j, p j * @OnlineAlgorithm.cost k (Fin (k + 1)) m A (σ j) := by sorry

end KServer
