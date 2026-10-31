-- Prove2me | Theorems.Thm_ZeroOneSimplex_orderedShadowPivotRule_nonDegeneratePivots_le_dim
-- name    : ZeroOneSimplex.orderedShadowPivotRule_nonDegeneratePivots_le_dim
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:53.090998+00:00
-- url     : https://prove2.me/theorems/0af42ee5-a32e-42af-87fa-9f032e94f5ba
-- title:
--   Theorem 3 — the Ordered Shadow pivot rule reaches an optimum within $d$ non-degenerate pivots
-- statement:
--   **Theorem 3.** On any 0/1-LP of form (1) whose feasible region has dimension $d$, the Ordered Shadow pivot rule reaches an optimal solution by performing no more than $d$ non-degenerate pivots.
--
--   Precisely: let the LP $\max\{c^\top x: Ax=b,\ Dx\le d,\ x\ge0\}$ have integral $c$, $A$ of full row rank, and feasible region $P$ a nonempty polytope with vertices in $\{0,1\}^n$; let $d=\dim P$ and let $B^0$ be any feasible basis of the standard form. Then
--
--   1. **the rule runs and stops:** (a) a lexicographic run of the Ordered Shadow pivot rule from $B^0$ exists; (b) every lexicographic run from $B^0$ either ends at an optimal basis or extends by one more Phase 2 pivot with the same lexicographic order; (c) there is $N$ such that every lexicographic run from $B^0$ has at most $N$ Phase 2 pivots;
--   2. **it is optimal:** every run from $B^0$ that ends at an optimal basis ends at a vertex maximizing $c^\top x$ on $P$;
--   3. **the bound:** every run from $B^0$, with any choice of leaving variables, performs at most $d$ non-degenerate pivots.
--
--   The bound matches Naddef's bound $d$ on the diameter of 0/1 polytopes.
--
--   Differences from the source:
--   - encoding: the inequalities Dx ≤ d contain x ≥ 0 (assumption (ii), p.6) → x ≥ 0 is kept apart and D holds only the other inequalities; reason: the same feasible region; slacks are added only for the other inequalities, as on p.6
--   - encoding: P a 0/1 polytope → P nonempty and bounded with every extreme point in {0,1}ⁿ (IsZeroOneLP); reason: P is a compact convex set, so it is the convex hull of its extreme points; an empty P has no vertex and no basis
--   - generalization: c, b, d, A and D integral (p.2) → c integral; A, b, D, d real; reason: integrality of A, b, D, d is never used; integral data are a special case
--   - encoding: pivot direction z′ʲ(B) = A′_B⁻¹A′_j (pp.7, 11) → the unique w with A′w = 0, w_j = 1, w_k = 0 for nonbasic k ≠ j; reason: the printed formula has the wrong sign (the direction must satisfy A′w = 0); the ratio test (2) is unchanged
--   - reading: the Ordered Shadow pivot rule (no single definition; Definition 5, Theorem 7, Lemma 6, §3.4) → a run: Phase 1 degenerate pivots to a basis satisfying the slope condition on the whole basic cone, Phase 2 entering an improving direction of largest slope cᵀz/vᵀz; reason: the condition of Theorem 7 and Lemma 6 is stated on the whole cone; the generator-level test of the proof of Lemma 6 fails on the triangle of paper.md
--   - generalization: Phase 1 pivots enter directions with cᵀz > 0 (proof of Lemma 6) → Phase 1 is any sequence of degenerate pivots; reason: the bound holds after every such sequence; the printed restriction cannot reach the condition in general
--   - generalization: lexicographic leaving rule (p.25) → clauses 2 and 3 hold for every leaving choice allowed by the ratio test; reason: Theorem 7 uses no tie-break; termination (clause 1) uses the lexicographic rule
--   - encoding: the lexicographic method, started at B⁰ → right-hand-side perturbation b′ + Σ εⁱA′_{e(i)} started at the Phase 2 basis; reason: perturbation feasibility for all small ε > 0 is exactly the lexicographic ratio test; Phase 1 is finite by construction
--   - encoding: an optimal B⁰ not satisfying the condition: the printed algorithm stops at once → every run passes through a basis satisfying the condition; reason: at an optimal vertex every pivot is degenerate, so the count and clause 1 are unaffected
--   - encoding: d = dimension of the feasible region → d = finrank (vectorSpan P); reason: the dimension of the affine hull of P
--   - reading: reaches an optimal solution → clause 1: a lexicographic run exists, every non-terminal one extends by a Phase 2 pivot, and Phase 2 lengths are bounded; clause 2: a run ending at an optimal basis ends at a maximizer of c on P; reason: a count alone holds for the empty run; optimal is Step 1 of p.7, and a run may stay at an optimal vertex by degenerate pivots until its basis certifies it
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Theorem 3, p.4; proof p.26 (from Theorems 6 and 7, Lemma 6, §3.4)

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData
import Definitions.Def_ZeroOneSimplex_IsEdge
import Definitions.Def_ZeroOneSimplex_LPData_IsRun
set_option autoImplicit false

open Matrix

namespace ZeroOneSimplex

/-- **Theorem 3** (Black, De Loera, Kafer, Sanità, *On the Simplex method for 0/1 polytopes*,
arXiv:2111.14050v1, p.4). On any 0/1-LP of the form (1) whose feasible region has dimension `d`,
the Ordered Shadow pivot rule reaches an optimal solution by performing no more than `d`
non-degenerate pivots.

Let the LP (1) have integral `c`, `A` of full row rank, and a feasible region `P` that is a
nonempty polytope with 0/1 vertices, and let `B⁰` be any feasible basis of its standard form. Then
1. **the rule runs and stops**: (a) a lexicographic run from `B⁰` exists; (b) every lexicographic
   run from `B⁰` either ends at an optimal basis or extends by one more Phase 2 pivot (with the
   same lexicographic order); (c) the number of Phase 2 pivots `T − t₀` of the lexicographic runs
   from `B⁰` is bounded;
2. **it is optimal**: every run from `B⁰` ending at an optimal basis ends at a vertex maximizing
   `cᵀx` on `P`;
3. **the bound**: every run from `B⁰`, with any leaving choices, performs at most
   `d = dim P` non-degenerate pivots.

**Formalization Note.** The rule (`IsRun`) is assembled from Definition 5, Theorem 7, Lemma 6 and
§3.4: Phase 1 is any sequence of degenerate pivots reaching a basis that satisfies the condition
of Theorem 7 on the whole basic cone, Phase 2 enters an improving direction of largest slope.
Termination uses the lexicographic leaving rule, encoded by right-hand-side perturbation
(`IsLexRun`); the bound and optimality hold for every leaving choice. `d` is
`finrank (vectorSpan P)`. -/
theorem orderedShadowPivotRule_nonDegeneratePivots_le_dim {n m p : ℕ} (L : LPData n m p)
    (hA : L.A.rank = m) (h01 : L.IsZeroOneLP) (B0 : Finset (Fin n ⊕ Fin p))
    (hB0 : L.IsFeasibleBasis B0) :
    ((∃ (T t0 : ℕ) (B : ℕ → Finset (Fin n ⊕ Fin p)) (e : Fin (m + p) → Fin n ⊕ Fin p),
          L.IsLexRun B0 T t0 B e) ∧
        (∀ (T t0 : ℕ) (B : ℕ → Finset (Fin n ⊕ Fin p)) (e : Fin (m + p) → Fin n ⊕ Fin p),
          L.IsLexRun B0 T t0 B e →
            L.IsOptimalBasis (B T) ∨
              ∃ B' : Finset (Fin n ⊕ Fin p),
                L.IsLexRun B0 (T + 1) t0 (fun t => if t ≤ T then B t else B') e) ∧
        ∃ N : ℕ, ∀ (T t0 : ℕ) (B : ℕ → Finset (Fin n ⊕ Fin p))
          (e : Fin (m + p) → Fin n ⊕ Fin p), L.IsLexRun B0 T t0 B e → T ≤ t0 + N) ∧
      (∀ (T t0 : ℕ) (B : ℕ → Finset (Fin n ⊕ Fin p)), L.IsRun B0 T t0 B →
        L.IsOptimalBasis (B T) → IsMaximizer L.feasibleRegion L.c (L.vertexOf (B T))) ∧
      ∀ (T t0 : ℕ) (B : ℕ → Finset (Fin n ⊕ Fin p)), L.IsRun B0 T t0 B →
        L.nonDegCount B T ≤ Module.finrank ℝ (vectorSpan ℝ L.feasibleRegion) := by sorry

end ZeroOneSimplex
