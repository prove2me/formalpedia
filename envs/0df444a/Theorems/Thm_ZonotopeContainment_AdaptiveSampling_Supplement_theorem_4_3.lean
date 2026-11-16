-- Prove2me | Theorems.Thm_ZonotopeContainment_AdaptiveSampling_Supplement_theorem_4_3
-- name    : ZonotopeContainment.AdaptiveSampling.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:49:55.751388+00:00
-- url     : https://prove2.me/theorems/6e6c80c5-457b-4f2f-9e83-fa7846d0edac
-- title:
--   Theorem 4.3 — no polynomial-query randomized algorithm decides gap containment of symmetric convex bodies at a factor $o(d/\log d)$
-- statement:
--   Let $s:\mathbb N\to\mathbb R$ be a gap factor with $s(d)\ge1$ for every $d$ and
--   $$s(d)\in o\!\left(\frac{d}{\log d}\right),\qquad\text{i.e.}\qquad \frac{s(d)\log d}{d}\longrightarrow0\quad(d\to\infty).$$
--   In $(K,Q)$-Gap-Containment with factor $s$ the input is a pair of convex bodies $K,Q\subseteq\mathbb R^d$ given by membership oracles; the answer Yes is valid when $K\subseteq Q$, the answer No is valid when $s(d)K\not\subseteq Q$.
--
--   Then there is no family of randomized algorithms $(A_d)_{d\in\mathbb N}$ such that
--
--   1. $A_d$ makes at most $q(d)\le C d^k+C$ membership queries (to $K$ or to $Q$, adaptively chosen) for some constants $C,k$, and
--   2. for all sufficiently large $d$ and every pair $K,Q$ of origin-symmetric convex bodies in $\mathbb R^d$ with $\tfrac1dB_2^d\subseteq K,Q\subseteq dB_2^d$, $A_d$ gives a valid answer with probability at least $2/3$ over its coins.
--
--   The algorithms may use any number of uniform coins and unbounded computation; they see the bodies only through exact membership queries. So the $O(d/\log d)$ guarantee available for general convex bodies by random sampling cannot be improved with polynomially many queries, even for centrally symmetric bodies.
--
--   **Formalization Note** The oracle model, the gap answer and the success count are the definitions of `ZonotopeContainment.AdaptiveSampling.Supplement.OracleModel`; success probability at least $2/3$ is written as $3\cdot\#\{\omega\text{ valid}\}\ge2\cdot2^{m}$.
--
--   Differences from the source:
--   - reading: "with high probability" → success probability at least 2/3 on every instance; reason: this is the paper's own threshold in Lemma 4.4 and the proof of Theorem 4.3 (pp. 13–14); refuting success ≥ 2/3 also refutes every larger threshold
--   - generalization: randomized polynomial time algorithm → any algorithm with polynomially many exact membership queries at arbitrary real points, any finite number of uniform coins and unbounded computation; reason: every randomized polynomial-time oracle algorithm is in this class, so nonexistence here implies the source's nonexistence
--   - generalization: decides correctly for each K, Q ⊆ ℝᵈ (all d) → correct only for all sufficiently large d and only on origin-symmetric bodies with radii 1/d and d; reason: an algorithm correct on all instances in all dimensions satisfies the weaker requirement, so this nonexistence implies the source's, including its "even when K and Q are centrally symmetric" clause
--   - encoding: convex bodies with 0 in the interior and radii in the oracle description → compact convex origin-symmetric sets with closedBall 0 (1/d) ⊆ K ⊆ closedBall 0 d; reason: the radii are fixed as functions of d and the class contains the paper's hard instances (P/s, P°) with P = B₂ᵈ or conv(B₂ᵈ, ±Rv), R ≤ √d, for large d
--   - encoding: s ∈ o(d/log d) with s ≥ 1 (§5 gap convention) → s : ℕ → ℝ, s d ≥ 1 for all d, s(d)·log d/d → 0; reason: the definition of little-o; a rational s is a special case
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), Theorem 4.3, p. 13 (proof pp. 13–14); oracle model §1.1 pp. 2–3; gap convention §5, p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Supplement_OracleModel

open Filter Topology

namespace ZonotopeContainment.AdaptiveSampling.Supplement

/-- Theorem 4.3, pp. 13–14: for s(d) = o(d / log d) no randomized algorithm family with
polynomially many membership queries answers (K, Q)-Gap-Containment correctly with
probability at least 2/3 on every pair of origin-symmetric bodies, not even when
correctness is only required in all sufficiently large dimensions. -/
theorem theorem_4_3 (s : ℕ → ℝ) (hs1 : ∀ d, 1 ≤ s d)
    (hs : Tendsto (fun d : ℕ => s d * Real.log d / d) atTop (𝓝 0)) :
    ¬ ∃ (q m : ℕ → ℕ) (C k : ℕ) (A : ∀ d, QueryAlg d (q d) (m d)),
        (∀ d, q d ≤ C * d ^ k + C) ∧
        ∀ᶠ d in atTop, ∀ K Q : Set (E d), SymBody d K → SymBody d Q →
          2 * 2 ^ (m d) ≤ 3 * successCount (A d) (s d) K Q := by sorry

end ZonotopeContainment.AdaptiveSampling.Supplement
