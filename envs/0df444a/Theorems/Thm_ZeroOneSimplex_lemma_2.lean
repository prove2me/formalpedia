-- Prove2me | Theorems.Thm_ZeroOneSimplex_lemma_2
-- name    : ZeroOneSimplex.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:50:39.88175+00:00
-- url     : https://prove2.me/theorems/ddae5200-adf4-4b52-933b-f20afdc40203
-- title:
--   Lemma 2 — a coherent monotone path passes through a $c$-maximum
-- statement:
--   Let $Q\subseteq\mathbb R^n$ be a polytope, $c\in\mathbb R^n$, $v\in\mathbb R^n\setminus\{0\}$, and let $\Gamma=[x^0,\dots,x^k]$ be a $c$-coherent $v$-monotone path in $Q$. Then there is $0\le i\le k$ such that $x^i$ maximizes $c$ on $Q$ and
--   $$
--   c^\top x^{j}<c^\top x^{j+1},\qquad v^\top x^{j}<v^\top x^{j+1}\qquad (0\le j<i),
--   $$
--   i.e. the portion of $\Gamma$ from $x^0$ to $x^i$ is both $c$-monotone and $v$-monotone.
--
--   Lemma 2 is why a Shadow rule reaches an optimum: following the upper path of the shadow, it climbs in $c$ until the top.
--
--   Differences from the source:
--   - encoding: upper path: vertices of π(Q) on or above the line L through u⁰ and u¹ → upper boundary of π(Q): points of π(Q) highest above their first coordinate; reason: the same path for a polygon; it is also defined when vᵀx is constant on Q (L undefined)
--   - encoding: a path [x⁰, …, xᵏ] → a sequence x : ℕ → ℝⁿ with a length k; reason: only x 0, …, x k matter
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Lemma 2, pp.13–14

import Mathlib
import Definitions.Def_ZeroOneSimplex_IsCoherentPath
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Lemma 2** (Black, De Loera, Kafer, Sanità, arXiv:2111.14050v1, pp.13–14). Consider the LP
`max {cᵀx : x ∈ Q}` for a polytope `Q`, let `v ≠ 0`, and let `x 0, …, x k` be a `c`-coherent
`v`-monotone path in `Q`. Then some `x i`, `0 ≤ i ≤ k`, maximizes `c` on `Q`, and the portion of
the path from `x 0` to `x i` is both `c`-monotone and `v`-monotone.

**Formalization Note.** Coherence uses the upper boundary of `π(Q)` for the paper's upper path
(see `upperBoundary`). -/
theorem lemma_2 {n : ℕ} (Q : Set (Fin n → ℝ)) (hQ : IsPolytope Q) (c v : Fin n → ℝ)
    (hv : v ≠ 0) (x : ℕ → Fin n → ℝ) (k : ℕ) (hΓ : IsCoherentPath Q c v x k) :
    ∃ i ≤ k, IsMaximizer Q c (x i) ∧
      ∀ j < i, c ⬝ᵥ x j < c ⬝ᵥ x (j + 1) ∧ v ⬝ᵥ x j < v ⬝ᵥ x (j + 1) := by sorry

end ZeroOneSimplex
