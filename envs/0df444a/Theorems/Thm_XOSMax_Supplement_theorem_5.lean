-- Prove2me | Theorems.Thm_XOSMax_Supplement_theorem_5
-- name    : XOSMax.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:36:51.959537+00:00
-- url     : https://prove2.me/theorems/b3001c55-5bf4-428f-a1ed-27f3ec610d6b
-- title:
--   Theorem 5 (corrected: zero-error randomized algorithms) — exponential lower bound below $k-1$
-- statement:
--   For every $k\ge3$ and $0<\varepsilon<k-1$, there are $c,C>0$ and $N$ such that, for every $n\ge N$, a distribution of $k$-XOS functions on $[n]$ has the following property. Every randomized algorithm that returns a $(k-1-\varepsilon)$-maximizer on every run and every instance in the support of the distribution makes at least
--   $$
--   \delta\,2^{C n^c}
--   $$
--   oracle calls with probability at least $1-\delta$, for every $\delta\in(0,1)$.
--
--   The source states this for randomized $(k-1-\varepsilon)$-approximation algorithms, which its p.2 definition makes correct only in expectation; under that definition the statement is false (see the first difference), so the class is corrected to zero-error algorithms, which is what the proof and Lemma 16 treat.
--
--   Differences from the source:
--   - correction: a randomized $(k-1-\varepsilon)$-approximation algorithm, defined on p.2 by its expected value → a zero-error randomized algorithm whose every supported run returns a $(k-1-\varepsilon)$-maximizer; reason: the printed statement is false: with constant probability $q$ run exhaustive search and otherwise Algorithm 4 ($O(k^2n)$ calls, a $(k-1)$-maximizer); for $q\ge(1/(k-1-\varepsilon)-1/(k-1))/(1-1/(k-1))$ this is an approximation in expectation, yet it makes $O(k^2n)$ calls with probability $1-q>\delta$ for small $\delta$
--   - generalization: an approximation algorithm for $k$-XOS maximization, correct on every $k$-XOS input → correctness required only on the instances in the support of the hard distribution; reason: a weaker hypothesis on the algorithm, so the Lean bound applies to every algorithm the source's statement covers and to more
--   - encoding: every $\varepsilon>0$ → $0<\varepsilon<k-1$; reason: $k-1-\varepsilon$ must be a positive approximation ratio (the source defines ratios only for values at least one), and at ratio $0$ Lean's $1/0=0$ would make $\emptyset$ a maximizer
--   - encoding: $2^{\Omega(n^c)}$ → $2^{C n^c}$ for positive $C$, after a threshold $N$; reason: this is the quantified meaning of the asymptotic lower bound and includes the proof's padding to all large $n$
--   - encoding: probability over the hard instance and the algorithm → the iterated probability-weighted sum over two PMFs; reason: this is the product probability
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Theorem 5, p.2, restated with proof p.12

import Mathlib
import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_IsMaximizerApprox
import Definitions.Def_XOSMax_Supplement_RandomizedProg

namespace XOSMax.Supplement

open XOSMax OracleProg

/-- **Theorem 5 (zero-error reading supported by the proof).** Beating ratio `k-1` for `k`-XOS
maximization requires exponentially many value-oracle calls with high probability
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Theorem 5, pp.2 and 12).

**Formalization Note** The source's in-expectation definition of a randomized approximation
algorithm would make the displayed high-probability lower bound false: mixing exhaustive search
with a cheap failing run preserves an expected approximation while making few calls with constant
probability. The proof instead treats algorithms that find a sufficiently valuable set on every
run. Accordingly, `A` must return a `(k-1-ε)`-maximizer for every program in its support and every
instance in the hard distribution's support. Constants may depend on `k, ε`, never on `n`; dummy
elements cover all sufficiently large `n`. -/
theorem theorem_5 :
    ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε < k - 1 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ D : PMF (Finset (Fin n) → ℝ),
          (∀ f ∈ D.support, IsKXOS k f) ∧
          ∀ A : RandomizedProg (Fin n) (Finset (Fin n)),
            (∀ f ∈ D.support, ∀ p ∈ A.support,
              IsMaximizerApprox Finset.univ (k - 1 - ε) f (run f p).1) →
            ∀ δ : ℝ, 0 < δ → δ < 1 →
              1 - δ ≤ ∑' f, (D f).toReal *
                ∑' p, (A p).toReal *
                  if δ * Real.rpow 2 (C * Real.rpow n c) ≤ queries f p then 1 else 0 := by sorry

end XOSMax.Supplement
