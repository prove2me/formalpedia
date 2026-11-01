-- Prove2me | Theorems.Thm_XOSMax_lemma_12_sandwich
-- name    : XOSMax.lemma_12_sandwich
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:20.32599+00:00
-- url     : https://prove2.me/theorems/f8aa9544-bf8c-443e-81b3-18a6c2fb7983
-- title:
--   Lemma 12 (proof) — $V_p\subseteq X^*\subseteq Y_p$
-- statement:
--   Let $f$ be represented by clauses $f_1,\dots,f_k$ on a ground set $V$, with $f(v)>0$ for all $v\in V$. For an index $p$, let $V_p=V^*_p$ be the clique of $p$, let $X^*=\{v\in V: f_p(v)>0\}$, and let
--   $$
--   Y_p=V_p\cup\{\,v\in V\setminus V_p: f(V_p+v)>f(V_p)\,\}
--   $$
--   be the set computed by Line 7 from $V_p$. Then
--   $$
--   V_p\subseteq X^*\subseteq Y_p .
--   $$
--   This places the optimal set between two sets the algorithm has computed. It is the starting point of the two cases in the proof of Lemma 12.
--
--   Differences from the source:
--   - encoding: the ground set $V$ → the Finset `L.toFinset` of a list `L` of a type `E` (repetitions are not excluded, since `buildY` scans `L` in order and a repeated element changes nothing); reason: the milestones run on the part of the ground set that survives the preprocessing, and list order resolves the free choices of the paper
--   - generalization: $\ell=k$ and $X^*$ a maximizer → every index $p$, with neither assumption; reason: the inclusions need neither, and the source case is an instance
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Lemma 12, proof, p.8, "we have Vp ⊆ X* ⊆ Yp"

import Mathlib
import Definitions.Def_XOSMax_Represents
import Definitions.Def_XOSMax_cliqueWrt
import Definitions.Def_XOSMax_buildY

namespace XOSMax

open OracleProg

/-- The inclusions in the proof of Lemma 12: with `V_p = V*_p`, `X* = { v ∈ V | f_p(v) > 0 }` and `Y_p`
built from `V_p` as in Line 7, "we have Vp ⊆ X* ⊆ Yp (recall the proof of Lemma 9)" (Filmus, Kawase,
Kobayashi & Yamaguchi, arXiv:1811.09045v3, Lemma 12, proof, p.8).

**Formalization Note** `V = L.toFinset`. The statement is for every index `p`: neither `ℓ = k` nor
the maximality of `X*` is needed for these inclusions. -/
theorem lemma_12_sandwich {E : Type} [DecidableEq E] (L : List E) {k : ℕ}
    (w : Fin k → E → ℝ) (f : Finset E → ℝ) (hw : Represents w f)
    (hpos : ∀ v ∈ L, 0 < f {v}) (p : Fin k) :
    cliqueWrt L.toFinset w f p ⊆ L.toFinset.filter (fun v => 0 < w p v) ∧
    L.toFinset.filter (fun v => 0 < w p v) ⊆
      (run f (buildY L (cliqueWrt L.toFinset w f p))).1 := by sorry

end XOSMax
