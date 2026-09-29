-- Prove2me | Theorems.Thm_KServer_mss_randomized_lower_bound
-- name    : KServer.mss_randomized_lower_bound
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-04T21:33:14.206412+00:00
-- url     : https://prove2.me/theorems/50fba9b1-9e06-438e-9566-ec7e85e9fe5c
-- title:
--   BCR 2023, Theorem 11 — $\Omega(\log^2 k)$ lower bound for small set chasing on $k+1$ points
-- statement:
--   **An existential $\Omega(\log^2 k)$ lower bound for small set chasing on $k+1$ points, in distributional (Yao) form.**
--
--   Small set chasing — historically *metrical service systems* (MSS) — is the following online problem. A single server (the *evader*) lives in a metric space $(M,d)$ and starts at a point $x_0$. The adversary presents a finite sequence $\sigma = (S_1,\dots,S_T)$ of nonempty subsets of $M$; upon seeing $S_j$ the evader must move to a point of $S_j$, and it pays the distance travelled. Its total cost is
--   $$\mathrm{cost}_E(\sigma) \;=\; \sum_{j=1}^{T} d\bigl(E(\sigma_{\le j-1}),\, E(\sigma_{\le j})\bigr),$$
--   where $E(\sigma_{\le j})$ is the evader's position after the first $j$ requests, so the algorithm is online and deterministic. The offline optimum $\mathrm{OPT}(x_0,\sigma)$ is the least total movement of a path that starts at $x_0$ and enters every requested set.
--
--   The statement asserts that there are a constant $c>0$ and a threshold $k_0$ such that for every $k \ge k_0$ there is a metric on the $(k+1)$-point set for which small set chasing is hard *in the distributional sense of Yao's principle*: for every target level $N$ there is a finitely supported probability distribution $p_1,\dots,p_n$ over request sequences $\sigma^{(1)},\dots,\sigma^{(n)}$, all of whose requested sets are nonempty, such that
--
--   1. the expected offline optimum is at least $N$, from *every* starting point $x_0$:
--   $$N \;\le\; \sum_{j=1}^{n} p_j \,\mathrm{OPT}(x_0, \sigma^{(j)});$$
--
--   2. every deterministic online evader $E$ satisfies
--   $$c\,(\log k)^2 \sum_{j=1}^{n} p_j \,\mathrm{OPT}\bigl(E(\varepsilon), \sigma^{(j)}\bigr) \;\le\; \sum_{j=1}^{n} p_j \,\mathrm{cost}_E\bigl(\sigma^{(j)}\bigr),$$
--   where $E(\varepsilon)$ is the evader's initial position.
--
--   Because $N$ is arbitrary, the family of hard distributions drives the expected offline cost to infinity while keeping the multiplicative gap $c(\log k)^2$, which is exactly what is needed to defeat an arbitrary additive constant in the definition of the competitive ratio.
--
--   This is the combinatorial heart of the refutation of the randomized $k$-server conjecture: by the folklore equivalence between $(n-1)$-server on an $n$-point space and small set chasing on that space (the unique unoccupied point plays the role of the evader), together with Yao's minimax principle, it yields an $\Omega(\log^2 k)$ lower bound on the randomized competitive ratio of the $k$-server problem on $(k+1)$-point metric spaces.
--
--   **Formalization Note** The metric is existentially quantified as a `MetricSpace (Fin (k + 1))` instance, so the carrier has exactly $k+1$ points. The distributional form (Definition 2 of the source) is used rather than the randomized form, so no measure theory is needed here: the distribution is a finite convex combination and the bound is stated for deterministic evaders. The multiplicative form carries no additive constant; the additive slack of the source's statement is absorbed by letting the distribution depend on $N$.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, https://arxiv.org/abs/2211.05753, Section 4, Theorem 11 (existence, for each n, of an n-point metric space with C_rand^MSS(M, n-1) = Omega(log^2 n)), stated in the distributional form of their Definition 2 and combined with their Theorem 3 (Yao's minimax principle); here n = k+1.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader

namespace KServer

theorem mss_randomized_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ m : MetricSpace (Fin (k + 1)),
        ∀ N : ℝ, ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → List (Set (Fin (k + 1)))),
          (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
          (∀ j, ∀ S ∈ σ j, S.Nonempty) ∧
          (∀ x₀ : Fin (k + 1),
            N ≤ ∑ j, p j * @evaderOfflineCost (Fin (k + 1)) m x₀ (σ j)) ∧
          (∀ E : @EvaderAlgorithm (Fin (k + 1)) m,
            c * Real.log k ^ 2
                * ∑ j, p j * @evaderOfflineCost (Fin (k + 1)) m
                    (@EvaderAlgorithm.pos (Fin (k + 1)) m E []) (σ j)
              ≤ ∑ j, p j * @EvaderAlgorithm.cost (Fin (k + 1)) m E (σ j)) := by sorry

end KServer
