-- Prove2me | Theorems.Thm_XOSMax_Supplement_theorem_3
-- name    : XOSMax.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:35:47.487468+00:00
-- url     : https://prove2.me/theorems/5cbe2145-e56f-490e-9a80-7c837c5d54ea
-- title:
--   Theorem 3 (corrected: zero-error randomized algorithms) — exponential and super-polynomial lower bounds for general XOS
-- statement:
--   **Part 1.** For every $\varepsilon>0$ there are $c,C>0$ and $N$ such that, for every $n\ge N$, a distribution of XOS functions on $[n]$ has the following property. Every randomized algorithm that returns an $n^{1-\varepsilon}$-maximizer on every run and every instance in the support of the distribution makes at least
--   $$
--   \delta\,2^{C n^c}
--   $$
--   oracle calls with probability at least $1-\delta$, for every $\delta\in(0,1)$.
--
--   **Part 2.** There is a family of distributions $D_n$ of XOS functions on $[n]$ such that, for every ratio function $\alpha(n)\ge1$ with $\alpha(n)=o(n/\log n)$, there are $h(n)\to\infty$ and $N$ with the following property: for every $n\ge N$, every randomized algorithm that returns an $\alpha(n)$-maximizer on every run and every instance in the support of $D_n$ makes at least $\delta\,n^{h(n)}$ oracle calls with probability at least $1-\delta$, for every $\delta\in(0,1)$.
--
--   The source states both parts for randomized approximation algorithms, which its p.2 definition makes correct only in expectation; under that definition both parts are false (see the first difference), so the class is corrected to zero-error algorithms, which is what the proof and Lemma 16 treat.
--
--   Differences from the source:
--   - correction: a randomized $n^{1-\varepsilon}$- (resp. $o(n/\log n)$-) approximation algorithm, defined on p.2 by its expected value → a zero-error randomized algorithm whose every supported run returns an $\alpha$-maximizer; reason: the printed statement is false: with probability $q_n=\alpha(n)^{-1}$ run exhaustive search and otherwise return the best positive singleton ($n$ calls, an $n$-maximizer of every XOS function); this is an $\alpha$-approximation in expectation, yet it makes $n$ calls with probability $1-q_n\to1$
--   - generalization: an approximation algorithm for XOS maximization, correct on every XOS input → correctness required only on the support of the hard distribution; reason: a weaker hypothesis on the algorithm, so the bounds cover every algorithm of the source's statement and more
--   - reading: "there exists a distribution … such that any randomized $o(n/\log n)$-approximation algorithm calls the value oracle at least $\delta\cdot n^{\omega(1)}$ times" → one family $D_n$ chosen before the ratio function $\alpha=o(n/\log n)$, then $h\to\infty$ depending on $\alpha$ only, a threshold $N$ uniform in the algorithm and $\delta$; reason: this is the printed quantifier order (the distribution precedes the algorithm and hence its ratio); the proof's instance with threshold $\tau=\omega(\log n)$ supports only the order with the distribution chosen after the ratio, which is weaker and is not used
--   - encoding: ratios $\alpha$ of Part 2 → $\alpha(n)\ge1$ for every $n$; reason: the source defines $\alpha$-maximizers only for $\alpha\ge1$, and $\alpha(n)=0$ would make $\emptyset$ a maximizer through Lean's $1/0=0$
--   - encoding: $2^{\Omega(n^c)}$ → $2^{Cn^c}$ for positive $C$ after a threshold $N$, the distribution depending on $n$; $n^{\omega(1)}$ → $n^{h(n)}$ with $h\to\infty$; reason: the quantified meaning of the asymptotic bounds; the proof's even-$n$ assumption is covered by padding
--   - encoding: probability over the instance and the algorithm → the iterated probability-weighted sum over two PMFs; reason: this is the product probability
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Theorem 3, p.2, restated with proof p.11

import Mathlib
import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_IsMaximizerApprox
import Definitions.Def_XOSMax_Supplement_RandomizedProg

namespace XOSMax.Supplement

open XOSMax OracleProg Filter Asymptotics

/-- **Theorem 3 (corrected: zero-error randomized algorithms).** Beating ratio `n^(1-ε)` for
general XOS maximization requires `δ·2^(Ω(n^c))` value-oracle calls with probability at least
`1-δ`; and one distribution of XOS instances forces every `o(n/log n)`-approximation algorithm to
make `δ·n^(ω(1))` calls with probability at least `1-δ` (Filmus, Kawase, Kobayashi & Yamaguchi,
arXiv:1811.09045v3, Theorem 3, p.2, restated p.11).

**Formalization Note** As for Theorem 5, the p.2 in-expectation definition of a randomized
approximation algorithm makes both clauses false (mix exhaustive search, with vanishing
probability, with the `n`-query best-singleton algorithm). The proof treats algorithms that find a
valuable set on every run, so `A` must return an `α`-maximizer on every program in its support and
every instance in the distribution's support. Part 1: `2^(Ω(n^c))` is `2^(C n^c)` with `C > 0`
after a threshold `N`; the distribution may depend on `n`. Part 2 keeps the printed quantifier
order: one family of distributions `D n` is fixed before the ratio `α = o(n/log n)` (with
`α ≥ 1`, the source's range of ratios), and `n^(ω(1))` is `n^(h n)` with `h → ∞`, `h` depending
only on `α`. `log` is the natural logarithm. -/
theorem theorem_3 :
    (∀ ε : ℝ, 0 < ε →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ D : PMF (Finset (Fin n) → ℝ),
          (∀ f ∈ D.support, ∃ k : ℕ, IsKXOS k f) ∧
          ∀ A : RandomizedProg (Fin n) (Finset (Fin n)),
            (∀ f ∈ D.support, ∀ p ∈ A.support,
              IsMaximizerApprox Finset.univ (Real.rpow n (1 - ε)) f (run f p).1) →
            ∀ δ : ℝ, 0 < δ → δ < 1 →
              1 - δ ≤ ∑' f, (D f).toReal *
                ∑' p, (A p).toReal *
                  if δ * Real.rpow 2 (C * Real.rpow n c) ≤ queries f p then 1 else 0) ∧
    (∃ D : (n : ℕ) → PMF (Finset (Fin n) → ℝ),
      (∀ n, ∀ f ∈ (D n).support, ∃ k : ℕ, IsKXOS k f) ∧
      ∀ α : ℕ → ℝ, (∀ n, 1 ≤ α n) →
        α =o[atTop] (fun n : ℕ => (n : ℝ) / Real.log n) →
        ∃ h : ℕ → ℝ, Tendsto h atTop atTop ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ A : RandomizedProg (Fin n) (Finset (Fin n)),
            (∀ f ∈ (D n).support, ∀ p ∈ A.support,
              IsMaximizerApprox Finset.univ (α n) f (run f p).1) →
            ∀ δ : ℝ, 0 < δ → δ < 1 →
              1 - δ ≤ ∑' f, (D n f).toReal *
                ∑' p, (A p).toReal *
                  if δ * Real.rpow n (h n) ≤ queries f p then 1 else 0) := by sorry

end XOSMax.Supplement
