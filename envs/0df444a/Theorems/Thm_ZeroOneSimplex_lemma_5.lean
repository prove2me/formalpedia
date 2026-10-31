-- Prove2me | Theorems.Thm_ZeroOneSimplex_lemma_5
-- name    : ZeroOneSimplex.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:20.86533+00:00
-- url     : https://prove2.me/theorems/c825294d-3a2e-4a38-80b1-f0802ec329ed
-- title:
--   Lemma 5 — the $f$-minimal improving path has length at most $d$
-- statement:
--   Consider a 0/1-LP of form (1) with feasible region $P$ of dimension $d$, and an initial vertex $x^0$ of $P$. Let $f(u)=\max(\{k: u(k)\ne x^0(k)\}\cup\{0\})$. Build a path $\Gamma=[x^0,x^1,\dots]$ on $P$: given $x^i$, let $N_{\min}(x^i)$ be the set of $f$-minimal $c$-improving neighbors of $x^i$, and let $x^{i+1}$ be a $c$-maximum of $N_{\min}(x^i)$. Then every such path $[x^0,\dots,x^k]$ has
--   $$
--   k\le d=\dim P .
--   $$
--
--   This is the combinatorial core of the $d$ bound: the path climbs a chain of faces of strictly increasing dimension.
--
--   Differences from the source:
--   - encoding: the inequalities Dx ≤ d contain x ≥ 0 (assumption (ii), p.6) → x ≥ 0 is kept apart and D holds only the other inequalities; reason: the same feasible region; slacks are added only for the other inequalities, as on p.6
--   - encoding: P a 0/1 polytope → P nonempty and bounded with every extreme point in {0,1}ⁿ (IsZeroOneLP); reason: P is a compact convex set, so it is the convex hull of its extreme points; an empty P has no vertex and no basis
--   - generalization: c, b, d, A and D integral (p.2) → c integral; A, b, D, d real; reason: integrality of A, b, D, d is never used; integral data are a special case
--   - generalization: A of full row rank (assumption (i), p.6) → not assumed; reason: the statement concerns the feasible region P and no basis; full-rank instances are a special case
--   - encoding: coordinates k = 1, …, n → coordinates Fin n, the paper's coordinate k being k.val + 1 (exponents of c*, f and κ are 1-based); reason: Lean indexing; the same vectors and the same values of f
--   - reading: x^{i+1} is the c-maximum of N_min(x^i) → x^{i+1} is any c-maximum of N_min(x^i), and every finite initial part of the path is bounded; reason: the c-maximum need not be unique; the proof works for every choice
--   - encoding: a path [x⁰, …, xᵏ] → a sequence x : ℕ → ℝⁿ with a length k; reason: only x 0, …, x k matter
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Lemma 5, p.17

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData
import Definitions.Def_ZeroOneSimplex_IsLemma5Path
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Lemma 5** (Black, De Loera, Kafer, Sanità, arXiv:2111.14050v1, p.17). Consider a 0/1-LP of
the form (1) with feasible region `P` of dimension `d`, and an initial vertex `x⁰` of `P`. Build a
path from `x⁰` by moving from `x i` to a `c`-maximum of `N_min(x i)`, the set of `f`-minimal
`c`-improving neighbors of `x i`, where `f(u) = max({k : u(k) − x⁰(k) ≠ 0} ∪ {0})`. Every such
path `x 0, …, x k` has length `k ≤ d = dim P`. -/
theorem lemma_5 {n m p : ℕ} (L : LPData n m p) (h01 : L.IsZeroOneLP) (x : ℕ → Fin n → ℝ)
    (k : ℕ) (hΓ : IsLemma5Path L.feasibleRegion L.c (x 0) x k) :
    k ≤ Module.finrank ℝ (vectorSpan ℝ L.feasibleRegion) := by sorry

end ZeroOneSimplex
