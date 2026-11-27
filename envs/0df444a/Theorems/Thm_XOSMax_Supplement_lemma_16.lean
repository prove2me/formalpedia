-- Prove2me | Theorems.Thm_XOSMax_Supplement_lemma_16
-- name    : XOSMax.Supplement.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:36:21.401357+00:00
-- url     : https://prove2.me/theorems/8ae2b050-6429-4c2b-a742-ad65c6e25c39
-- title:
--   Lemma 16 — query lower bound for the hidden-subset instance
-- statement:
--   Let $1\le t\le s\le\hat n$, choose $S$ uniformly among the $s$-subsets of $[\hat n]$, and set $\hat f_S(X)=1$ exactly when $X\subseteq S$ and $|X|\ge t$. For every $\delta\in(0,1)$, any randomized algorithm that always finds such a query makes at least
--   $$
--   \delta(\hat n/s)^t
--   $$
--   oracle calls with probability at least $1-\delta$ over $S$ and its coins.
--
--   Differences from the source:
--   - reading: an algorithm "to find $X$ with $\hat f(X)=1$" → on every supported run, some oracle query receives answer $1$; reason: this is the event bounded in the proof, while an output-only reading is false
--   - encoding: uniform $S$ and randomized coins → a finite average over $s$-subsets and a probability-weighted sum over deterministic programs; reason: this is their product probability
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Lemma 16, p.10

import Mathlib
import Definitions.Def_XOSMax_Supplement_RandomizedProg

namespace XOSMax.Supplement

open XOSMax OracleProg

/-- **Lemma 16.** If `S` is uniform among the `s`-subsets of `[n]`, every possibly randomized
oracle algorithm that always finds a query `X ⊆ S` with `|X| ≥ t` uses at least
`δ (n/s)^t` queries with probability at least `1-δ`
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Lemma 16, p.10).

**Formalization Note** "Find" means that some oracle call returns `1`, exactly as in the proof; an
output-only reading is false. The outer finite average is over uniform `s`-subsets, while the inner
sum is over the algorithm's coins. The algorithm distribution is fixed before the hidden set `S`.
-/
theorem lemma_16 (n s t : ℕ) (ht : 1 ≤ t) (hts : t ≤ s) (hsn : s ≤ n)
    (A : RandomizedProg (Fin n) (Finset (Fin n)))
    (hfind : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, ∀ p ∈ A.support,
      ∃ q ∈ (trace (hardInstance S t) p).toFinset, q.2 = 1) :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      1 - δ ≤
        (1 / ((Finset.univ : Finset (Fin n)).powersetCard s).card) *
          ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
            ∑' p, (A p).toReal *
              if δ * Real.rpow ((n : ℝ) / s) t ≤ queries (hardInstance S t) p
              then 1 else 0 := by sorry

end XOSMax.Supplement
