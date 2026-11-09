-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_singleton_projection
-- name    : ZLIPPadding.Padding.singleton_projection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:40.81004+00:00
-- url     : https://prove2.me/theorems/5f2ad5fd-8935-4512-93aa-d786cc96877b
-- title:
--   Lemma 7.2 — Singleton projection
-- statement:
--   Let $n\geq1$, $N\geq n$ and $\gamma\geq1$. Let $\mu$ be a signed-permutation-invariant law on nonzero integer vectors in dimension $N$, all of squared norm at most $\gamma^2$. Conditional on any orbit of positive probability, let $k$ be its support size and let $J$ count its nonzero coordinates among the first $n$ positions. Then $1\leq k\leq\gamma^2$, and
--   $$p_k:=\Pr[J=1\mid\mathcal O]=\frac{n\binom{N-n}{k-1}}{\binom Nk}=\frac{nk}{N}\frac{\binom{N-n}{k-1}}{\binom{N-1}{k-1}}.$$
--   If $n\gamma^2/N\leq1/4$, then
--   $$p_k\geq\frac{3nk}{4N}\geq\frac{3n}{4N}.$$
--   The ideal randomized approximate-oracle output is such a law, with $\gamma=\Gamma(N)$. The bound is uniform over admissible orbit mixtures, without any lower bound on an individual orbit's probability.
--
--   Differences from the source:
--   - generalization: the ideal randomized oracle output law → any signed-permutation-invariant law with the same nonzero norm bound; reason: Corollary 2.6 and Lemma 2.2 make every source output law such a law, including arbitrary orbit mixtures
--   - encoding: conditional probability on an output orbit → ratio of joint event probability to the positive orbit probability; reason: positive orbit mass is explicit; all binomial ratios are real ratios
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 29 (PDF p. 30), Lemma 7.2

import Definitions.Def_ZLIPPadding_Padding_Laws

namespace ZLIPPadding.Padding
/-- Lemma 7.2, printed p.29 / PDF p.30. Generalized to every signed-invariant
hidden-coordinate law; ideal randomized oracle laws are such laws. -/
theorem singleton_projection (n N : ℕ) (hn : 0 < n) (hnN : n ≤ N)
    (γ : ℝ) (hγ : 1 ≤ γ) (μ : PMF (ZVec N))
    (hinv : SignedInvariant μ)
    (hbound : ∀ z, μ z ≠ 0 → z ≠ 0 ∧ (qnorm (1 : ZMat N) z : ℝ) ≤ γ^2)
    (a : ZVec N) (horbit : mass μ (signedOrbit a) ≠ 0) :
    let k := supportSize a
    let p := prob μ ({z | z ∈ signedOrbit a ∧ retainedSize n z = 1}) /
      prob μ (signedOrbit a)
    (1 ≤ k ∧ (k : ℝ) ≤ γ^2) ∧
    p = (n : ℝ) * (Nat.choose (N-n) (k-1) : ℝ) / (Nat.choose N k : ℝ) ∧
    p = ((n : ℝ)*k/N) *
      ((Nat.choose (N-n) (k-1) : ℝ) / (Nat.choose (N-1) (k-1) : ℝ)) ∧
    ((n : ℝ)*γ^2/N ≤ 1/4 →
      p ≥ 3*(n : ℝ)*k/(4*N) ∧ 3*(n : ℝ)*k/(4*N) ≥ 3*(n : ℝ)/(4*N)) := by sorry
end ZLIPPadding.Padding
