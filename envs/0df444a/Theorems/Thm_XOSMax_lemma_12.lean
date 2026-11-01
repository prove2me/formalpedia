-- Prove2me | Theorems.Thm_XOSMax_lemma_12
-- name    : XOSMax.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:28.350636+00:00
-- url     : https://prove2.me/theorems/652c2ef2-dca9-4e40-aeab-5637872c2f63
-- title:
--   Lemma 12 — Algorithm 4 returns a $(k-1)$-maximizer
-- statement:
--   Let $k\ge2$ and let $f$ be a $k$-XOS function on a nonempty ground set $V$ with $f(v)>0$ for all $v\in V$. The output $\tilde X$ of Algorithm 4 is a $(k-1)$-maximizer of $f$:
--   $$
--   \tilde X\subseteq V,\qquad f(\tilde X)\ge\frac1{k-1}\max_{X\subseteq V}f(X).
--   $$
--   The ratio is the width of any representation, and the same output serves every $k$ for which $f$ is $k$-XOS.
--
--   With Lemma 11 this is Theorem 4 for inputs satisfying $f(v)>0$.
--
--   Differences from the source:
--   - encoding: the ground set $V$ → the Finset `L.toFinset` of a repetition-free list `L` of a type `E`, with "pick" and "foreach" in the order of `L`; reason: the milestones run on the part of the ground set that survives the preprocessing, and list order resolves the free choices of the paper
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Lemma 12, p.8

import Mathlib
import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_IsMaximizerApprox
import Definitions.Def_XOSMax_alg4

namespace XOSMax

open OracleProg

/-- **Lemma 12**: "Algorithm 4 returns a (k − 1)-maximizer X̃ of f" (Filmus, Kawase, Kobayashi &
Yamaguchi, arXiv:1811.09045v3, Lemma 12, p.8).

**Formalization Note** The ground set `V` is `L.toFinset`, nonempty and without repetition, and
`f(v) > 0` on `V` as in the input of Algorithm 4. The ratio is the real number `k − 1`, with no
truncated subtraction. -/
theorem lemma_12 {E : Type} [DecidableEq E] (L : List E) (hL : L.Nodup) (hne : L ≠ []) {k : ℕ}
    (hk : 2 ≤ k) (f : Finset E → ℝ) (hf : IsKXOS k f) (hpos : ∀ v ∈ L, 0 < f {v}) :
    IsMaximizerApprox L.toFinset ((k : ℝ) - 1) f (run f (alg4 L)).1 := by sorry

end XOSMax
