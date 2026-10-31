-- Prove2me | Theorems.Thm_ZeroOneSimplex_theorem_6
-- name    : ZeroOneSimplex.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:39.023457+00:00
-- url     : https://prove2.me/theorems/87237bed-4808-40d2-9309-77a467c66bc3
-- title:
--   Theorem 6 — the Ordered Shadow rule follows a Lemma 5 path, at most $d$ steps
-- statement:
--   Consider a 0/1-LP of form (1) with feasible region $P$ of dimension $d$. Let $[x^0,\dots,x^k]$ be a path of the Ordered Shadow rule: $x^0$ is a vertex, $v$ is the Ordered Shadow vector of $x^0$, each $x^{i+1}$ is a Shadow rule step from $x^i$ for $(c,v)$, and no $x^i$ with $i<k$ maximizes $c$ on $P$. Then
--
--   1. $[x^0,\dots,x^k]$ is a path as described in Lemma 5;
--   2. $k\le d$;
--   3. if $x^k$ does not maximize $c$ on $P$, the rule can take a further step from $x^k$.
--
--   Hence the Ordered Shadow rule arrives at an optimal solution within $d$ steps.
--
--   Differences from the source:
--   - encoding: the inequalities Dx ≤ d contain x ≥ 0 (assumption (ii), p.6) → x ≥ 0 is kept apart and D holds only the other inequalities; reason: the same feasible region; slacks are added only for the other inequalities, as on p.6
--   - encoding: P a 0/1 polytope → P nonempty and bounded with every extreme point in {0,1}ⁿ (IsZeroOneLP); reason: P is a compact convex set, so it is the convex hull of its extreme points; an empty P has no vertex and no basis
--   - generalization: c, b, d, A and D integral (p.2) → c integral; A, b, D, d real; reason: integrality of A, b, D, d is never used; integral data are a special case
--   - generalization: A of full row rank (assumption (i), p.6) → not assumed; reason: the statement concerns the feasible region P and no basis; full-rank instances are a special case
--   - encoding: coordinates k = 1, …, n → coordinates Fin n, the paper's coordinate k being k.val + 1 (exponents of c*, f and κ are 1-based); reason: Lean indexing; the same vectors and the same values of f
--   - reading: the number of steps taken by the Ordered Shadow rule to arrive at an optimal solution is at most d → every rule path that has not met a c-maximum before its end is a Lemma 5 path of length ≤ d, and a further step exists while the current vertex is not a c-maximum; reason: the rule stops at an optimal solution (Definition 3: 'to an optimal LP solution'); clause 3 is 'arrives'
--   - encoding: a path [x⁰, …, xᵏ] → a sequence x : ℕ → ℝⁿ with a length k; reason: only x 0, …, x k matter
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Theorem 6, p.18

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData
import Definitions.Def_ZeroOneSimplex_IsShadowPath
import Definitions.Def_ZeroOneSimplex_IsLemma5Path
import Definitions.Def_ZeroOneSimplex_LPData_orderedShadowVec
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Theorem 6** (Black, De Loera, Kafer, Sanità, arXiv:2111.14050v1, p.18). Consider a 0/1-LP
of the form (1) with feasible region `P` of dimension `d`. The Ordered Shadow rule follows a path
as described in the statement of Lemma 5; hence it arrives at an optimal solution after at most
`d` steps. Precisely, let `x 0, …, x k` be a path of the Ordered Shadow rule: `x 0` is a vertex,
`v` is the vector of Definition 5 for `x⁰ = x 0`, every step is a Shadow rule step for `(c, v)`,
and no `x i` with `i < k` is a `c`-maximum of `P`. Then
1. `x 0, …, x k` is a path of Lemma 5 for `x⁰ = x 0`;
2. `k ≤ d = dim P`; and
3. if `x k` is not a `c`-maximum of `P`, the rule can take a further step from `x k`.

**Formalization Note.** Clause 3 together with clause 2 is "arrives at an optimal solution":
the rule never gets stuck before a `c`-maximum, and it reaches one within `d` steps. -/
theorem theorem_6 {n m p : ℕ} (L : LPData n m p) (h01 : L.IsZeroOneLP) (x : ℕ → Fin n → ℝ)
    (k : ℕ) (hΓ : IsShadowPath L.feasibleRegion L.c (L.orderedShadowVec (x 0)) x k) :
    IsLemma5Path L.feasibleRegion L.c (x 0) x k ∧
      k ≤ Module.finrank ℝ (vectorSpan ℝ L.feasibleRegion) ∧
      (¬ IsMaximizer L.feasibleRegion L.c (x k) →
        ∃ y, IsShadowStep L.feasibleRegion L.c (L.orderedShadowVec (x 0)) (x k) y) := by sorry

end ZeroOneSimplex
