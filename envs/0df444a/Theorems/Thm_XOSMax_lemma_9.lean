-- Prove2me | Theorems.Thm_XOSMax_lemma_9
-- name    : XOSMax.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:07.838044+00:00
-- url     : https://prove2.me/theorems/ea7b7b37-9e00-4d61-afe5-96fdce741cdb
-- title:
--   Lemma 9 — $Y_1$ or $Y_2$ is a maximizer
-- statement:
--   Let $f$ be a $2$-XOS function on a nonempty ground set $V$ with $f(v)>0$ for all $v\in V$, and suppose that $V_1\ne V$ at the end of Lines 1–3 of Algorithm 3. Then the sets $Y_1$ and $Y_2$ are computed, and at least one of them is a maximizer of $f$ over the subsets of $V$.
--
--   Together with Lemma 8 this gives the correctness of Algorithm 3, the linear-time exact algorithm for width $2$.
--
--   Differences from the source:
--   - encoding: the ground set $V$ → the Finset `L.toFinset` of a repetition-free list `L` of a type `E`, with "pick" and "foreach" in the order of `L`; reason: the milestones run on the part of the ground set that survives the preprocessing, and list order resolves the free choices of the paper
--   - reading: "At the end of Algorithm 3, Y1 or Y2" → the hypothesis $V_1\ne V$; reason: the sentence before the lemma reads "Suppose that V1 = V*1 ≠ V", and $Y_1,Y_2$ do not exist otherwise
--   - encoding: a maximizer → a `1`-maximizer in the sense of `IsMaximizerApprox`; reason: the two notions coincide
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Lemma 9, p.6

import Mathlib
import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_IsMaximizerApprox
import Definitions.Def_XOSMax_alg3

namespace XOSMax

open OracleProg

/-- **Lemma 9**: "At the end of Algorithm 3, Y1 or Y2 is a maximizer of f" (Filmus, Kawase, Kobayashi
& Yamaguchi, arXiv:1811.09045v3, Lemma 9, p.6).

**Formalization Note** The paper states the lemma after "Suppose that V1 = V*1 ≠ V", so it concerns
the branch past Line 4: if `V₁ ≠ V`, the sets `Y₁, Y₂` are computed and one of them is a `1`-maximizer
on `V = L.toFinset`. -/
theorem lemma_9 {E : Type} [DecidableEq E] (L : List E) (hL : L.Nodup) (hne : L ≠ [])
    (f : Finset E → ℝ) (hf : IsKXOS 2 f) (hpos : ∀ v ∈ L, 0 < f {v})
    (hV₁ : (run f (alg3 L)).1.V₁ ≠ L.toFinset) :
    ∃ V₂ Y₁ Y₂ : Finset E, (run f (alg3 L)).1.second = some (V₂, Y₁, Y₂) ∧
      (IsMaximizerApprox L.toFinset 1 f Y₁ ∨ IsMaximizerApprox L.toFinset 1 f Y₂) := by sorry

end XOSMax
