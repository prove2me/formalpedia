-- Prove2me | Theorems.Thm_ZeroOneSimplex_corollary_1
-- name    : ZeroOneSimplex.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:50:39.299098+00:00
-- url     : https://prove2.me/theorems/72ba6926-3486-442f-90c0-423621806978
-- title:
--   Corollary 1 — length of coherent monotone paths
-- statement:
--   Let $Q\subseteq\mathbb R^n$ be a polytope with vertex set $V$, $v\in\mathbb R^n\setminus\{0\}$, $F$ the face of $Q$ minimized by $v$, and $c$ any objective. Then
--
--   1. from every vertex $x$ of $Q$ that is a $c$-maximum of $F$ there is a $c$-coherent $v$-monotone path in $Q$ starting at $x$;
--   2. every $c$-coherent $v$-monotone path $[x^0,\dots,x^k]$ in $Q$ has length
--   $$
--   k\le |\{v^\top u : u\in V\}|-1 .
--   $$
--
--   Bounding the number of values of $v^\top x$ on vertices thus bounds the number of steps of a Shadow rule.
--
--   Differences from the source:
--   - encoding: upper path: vertices of π(Q) on or above the line L through u⁰ and u¹ → upper boundary of π(Q): points of π(Q) highest above their first coordinate; reason: the same path for a polygon; it is also defined when vᵀx is constant on Q (L undefined)
--   - reading: the c-coherent v-monotone path from a c-maximum of F to a c-maximum of Q has length at most |{vᵀu}| − 1 → clause 1: such a path exists from every vertex that is a c-maximum of F; clause 2: every c-coherent v-monotone path has k + 1 ≤ |{vᵀu}|; reason: the statement presupposes the path, and the proof of Lemma 5 uses that presupposition (p.18); the bound for the whole coherent path covers its portion up to a c-maximum of Q (Lemma 2); k + 1 ≤ … avoids ℕ subtraction
--   - encoding: a path [x⁰, …, xᵏ] → a sequence x : ℕ → ℝⁿ with a length k; reason: only x 0, …, x k matter
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Corollary 1, p.15

import Mathlib
import Definitions.Def_ZeroOneSimplex_IsCoherentPath
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Corollary 1** (Black, De Loera, Kafer, Sanità, arXiv:2111.14050v1, p.15). Let `Q ⊆ ℝⁿ` be
a polytope, `v ≠ 0`, `V` the vertex set of `Q`, `F` the face of `Q` minimized by `v`, and `c` any
objective. Then
1. from every vertex `x` of `Q` that is a `c`-maximum of `F` there is a `c`-coherent
   `v`-monotone path in `Q` starting at `x`; and
2. every `c`-coherent `v`-monotone path `x 0, …, x k` in `Q` has length
   `k ≤ |{vᵀu : u ∈ V}| − 1`, written `k + 1 ≤ |{vᵀu : u ∈ V}|`.

**Formalization Note.** The printed corollary speaks of "the" coherent path from a `c`-maximum of
`F`, presupposing that one exists; that presupposition is clause 1. The bound is stated for the
whole coherent path, which covers its portion up to a `c`-maximum of `Q` (Lemma 2). -/
theorem corollary_1 {n : ℕ} (Q : Set (Fin n → ℝ)) (hQ : IsPolytope Q) (v : Fin n → ℝ)
    (hv : v ≠ 0) (c : Fin n → ℝ) :
    (∀ x ∈ Set.extremePoints ℝ Q, IsMaximizer (vMinFace Q v) c x →
        ∃ (y : ℕ → Fin n → ℝ) (k : ℕ), y 0 = x ∧ IsCoherentPath Q c v y k) ∧
      ∀ (y : ℕ → Fin n → ℝ) (k : ℕ), IsCoherentPath Q c v y k →
        k + 1 ≤ ((fun u => v ⬝ᵥ u) '' Set.extremePoints ℝ Q).ncard := by sorry

end ZeroOneSimplex
