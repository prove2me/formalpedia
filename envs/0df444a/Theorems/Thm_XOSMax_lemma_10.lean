-- Prove2me | Theorems.Thm_XOSMax_lemma_10
-- name    : XOSMax.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:45.28236+00:00
-- url     : https://prove2.me/theorems/9f414b29-9756-4fdb-8683-81bfcef6d60c
-- title:
--   Lemma 10 — each $V_i$ is a clique, and $\ell\le k$
-- statement:
--   Let $f$ be represented by $k$ clauses on a ground set $V$, with $f(v)>0$ for all $v\in V$. For the list $V_1,\dots,V_\ell$ computed by Lines 1–6 of Algorithm 4:
--
--   1. each $V_i$ is a clique;
--   2. $\ell\le k$;
--   3. the sets $V_1,\dots,V_\ell$ are pairwise distinct;
--   4. $\bigcup_{i\in[\ell]}V_i=V$.
--
--   This bounds the number of iterations of the while-loop by the width, a number the algorithm does not know.
--
--   Differences from the source:
--   - encoding: the ground set $V$ → the Finset `L.toFinset` of a repetition-free list `L` of a type `E`, with "pick" and "foreach" in the order of `L`; reason: the milestones run on the part of the ground set that survives the preprocessing, and list order resolves the free choices of the paper
--   - generalization: each $V_i$ is a clique and $\ell\le k$ → also pairwise distinctness and $\bigcup_i V_i=V$; reason: both are stated in the proofs of Lemmas 10 and 12, and dropping them gives the lemma
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Lemma 10, p.7; items 3–4: Lemma 10, proof, p.7, "pairwise distinct", and Lemma 12, proof, p.8, "due to the condition of the while-loop (Line 2)"

import Mathlib
import Definitions.Def_XOSMax_Represents
import Definitions.Def_XOSMax_cliqueWrt
import Definitions.Def_XOSMax_cliquePhase

namespace XOSMax

open OracleProg

/-- **Lemma 10**: "At the end of Algorithm 4, each Vi (i ∈ [ℓ]) is a clique. In particular, ℓ ≤ k
holds" (Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Lemma 10, p.7).

**Formalization Note** The ground set `V` is `L.toFinset`, the width `k` is that of an arbitrary
representation `w`, and the list `V₁, …, V_ℓ` is the result of `cliquePhase`, which is Lines 1–6. The
last two clauses are facts the proofs of Lemmas 10 and 12 rely on: the `Vᵢ` are pairwise distinct (p.7),
and `⋃ᵢ Vᵢ = V` "due to the condition of the while-loop (Line 2)" (p.8). -/
theorem lemma_10 {E : Type} [DecidableEq E] (L : List E) (hL : L.Nodup) {k : ℕ}
    (w : Fin k → E → ℝ) (f : Finset E → ℝ) (hw : Represents w f)
    (hpos : ∀ v ∈ L, 0 < f {v}) :
    (∀ V' ∈ (run f (cliquePhase L)).1, ∃ j : Fin k, V' = cliqueWrt L.toFinset w f j) ∧
    (run f (cliquePhase L)).1.length ≤ k ∧
    (run f (cliquePhase L)).1.Nodup ∧
    (run f (cliquePhase L)).1.foldr (· ∪ ·) ∅ = L.toFinset := by sorry

end XOSMax
