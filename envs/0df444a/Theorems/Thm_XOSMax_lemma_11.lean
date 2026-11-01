-- Prove2me | Theorems.Thm_XOSMax_lemma_11
-- name    : XOSMax.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:46.167085+00:00
-- url     : https://prove2.me/theorems/00406915-49a2-4655-ba03-31c2d2994bfe
-- title:
--   Lemma 11 — Algorithm 4 runs in $O(k^2n)$ time
-- statement:
--   There is an absolute constant $C$ such that, for every finite list $L$ without repetition of length $n$, every $k\ge1$, and every $k$-XOS function $f$ with $f(v)>0$ on $L$, the cost of executing Algorithm 4 on $L$ against $f$ is at most
--   $$
--   C\,k^2\,n .
--   $$
--   The cost counts the value oracle calls and the elementary steps of the program, and $C$ does not depend on the ground set, on $k$ or on $f$.
--
--   The bound involves the width although the algorithm does not know it, through the number of cliques (Lemma 10) and the number of pairs of cliques.
--
--   Differences from the source:
--   - reading: "time" → value oracle calls plus charged elementary steps of the program; reason: §1, p.2 counts oracle calls and the proof of Lemma 11 also counts set constructions, so this bounds both
--   - encoding: $O(k^2n)$ → one natural number $C$ quantified before the type, the list, $k$ and $f$; reason: this is the meaning of the $O$-notation in the lemma
--   - encoding: any ground set → `E : Type`, and `L.length` for $n$; reason: every finite set has a copy in `Type`
--   - generalization: $k\ge2$ (§2.4) → $k\ge1$; reason: the bound also holds for additive functions, and restricting to $k\ge2$ gives the source claim
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Lemma 11, p.7

import Mathlib
import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_alg4

namespace XOSMax

open OracleProg

/-- **Lemma 11**: "Algorithm 4 can be implemented to run in O(k²n) time" (Filmus, Kawase, Kobayashi &
Yamaguchi, arXiv:1811.09045v3, Lemma 11, p.7).

**Formalization Note** `O(·)` is one constant `C`, chosen before the type `E`, the list `L`, the
width `k` and the function `f`. The cost is what `run` counts for `alg4`: value oracle calls plus
elementary steps, charged as in the docstrings of the programs. `n` is the length of `L`. -/
theorem lemma_11 : ∃ C : ℕ, ∀ (E : Type) [DecidableEq E] (L : List E), L.Nodup →
    ∀ (k : ℕ), 1 ≤ k → ∀ f : Finset E → ℝ, IsKXOS k f → (∀ v ∈ L, 0 < f {v}) →
      (run f (alg4 L)).2 ≤ C * k ^ 2 * L.length := by sorry

end XOSMax
