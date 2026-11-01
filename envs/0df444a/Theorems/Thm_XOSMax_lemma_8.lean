-- Prove2me | Theorems.Thm_XOSMax_lemma_8
-- name    : XOSMax.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:52.819987+00:00
-- url     : https://prove2.me/theorems/f714b65d-b40f-4238-9772-c55d748ff938
-- title:
--   Lemma 8 — $V_1$ and $V_2$ are the two cliques
-- statement:
--   Let $f$ be represented by two clauses on a nonempty ground set $V$, with $f(v)>0$ for all $v\in V$. At the end of Algorithm 3:
--
--   1. $V_1$ is a clique;
--   2. if $V_1=V$ then the algorithm has returned at Line 4, and $V_2$ is not computed;
--   3. if $V_1\ne V$ then $V_2$ is computed, $V_2\ne V_1$, the sets $V_1$ and $V_2$ are the cliques with respect to the two different clauses, and $V_1\cup V_2=V$.
--
--   The statement holds for every representation of width $2$ of $f$. It shows that the greedy scan recovers the cliques with no knowledge of the clauses.
--
--   Differences from the source:
--   - encoding: the ground set $V$ → the Finset `L.toFinset` of a repetition-free list `L` of a type `E`, with "pick" and "foreach" in the order of `L`; reason: the milestones run on the part of the ground set that survives the preprocessing, and list order resolves the free choices of the paper
--   - reading: "$V_2$ is the other clique" → $V_2\ne V_1$, and $V_1=V^*_i$, $V_2=V^*_j$ with $i\ne j$; reason: this is what "other" means, and it is what the proof derives
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Lemma 8, p.5

import Mathlib
import Definitions.Def_XOSMax_Represents
import Definitions.Def_XOSMax_cliqueWrt
import Definitions.Def_XOSMax_alg3

namespace XOSMax

open OracleProg

/-- **Lemma 8**: "At the end of Algorithm 3, V1 is a clique, and V2 is the other clique with
V1 ∪ V2 = V if it is computed (i.e., unless V = V1)" (Filmus, Kawase, Kobayashi & Yamaguchi,
arXiv:1811.09045v3, Lemma 8, p.5).

**Formalization Note** The ground set `V` is `L.toFinset`, for any repetition-free nonempty list `L`,
and `f` is any function with a representation `w` of width 2 and `f(v) > 0` on `V`. The third clause
says: `V₂` is computed exactly when `V₁ ≠ V`, the two cliques `V₁, V₂` are `V*₀, V*₁` in some order
and they are different, and they cover `V`. -/
theorem lemma_8 {E : Type} [DecidableEq E] (L : List E) (hL : L.Nodup) (hne : L ≠ [])
    (w : Fin 2 → E → ℝ) (f : Finset E → ℝ) (hw : Represents w f)
    (hpos : ∀ v ∈ L, 0 < f {v}) :
    (∃ i : Fin 2, (run f (alg3 L)).1.V₁ = cliqueWrt L.toFinset w f i) ∧
    ((run f (alg3 L)).1.V₁ = L.toFinset → (run f (alg3 L)).1.second = none) ∧
    ((run f (alg3 L)).1.V₁ ≠ L.toFinset →
      ∃ V₂ Y₁ Y₂ : Finset E, (run f (alg3 L)).1.second = some (V₂, Y₁, Y₂) ∧
        V₂ ≠ (run f (alg3 L)).1.V₁ ∧
        (∃ i j : Fin 2, i ≠ j ∧ (run f (alg3 L)).1.V₁ = cliqueWrt L.toFinset w f i ∧
          V₂ = cliqueWrt L.toFinset w f j) ∧
        (run f (alg3 L)).1.V₁ ∪ V₂ = L.toFinset) := by sorry

end XOSMax
