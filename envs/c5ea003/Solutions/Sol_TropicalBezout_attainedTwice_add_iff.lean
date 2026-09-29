-- Prove2me | solution 1 for TropicalBezout.attainedTwice_add_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:04:58.816198+00:00
-- url     : https://prove2.me/submissions/162a4446-71ff-4d8e-a31a-1e28ffe6616f

-- Sol generated from Bridges/AlgebraTropicalGeometry/TropicalBezoutFactorization.lean
import Mathlib
import Definitions.Def_Bridges_AlgebraTropicalGeometry_TropicalBezoutFactorization
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Bézout: factorization of tropical hypersurfaces and Newton polytopes

This file *extends* `Bridges.AlgebraTropicalGeometry.TropicalValuationLimitBridge`.  That file
established the bridge between a non-Archimedean valuation and tropical geometry, proving:

* `TropicalValuationBridge.kapranov_easy_direction` — the easy direction of the Fundamental
  Theorem of Tropical Geometry (tropicalization ⊆ corner locus), and
* `TropicalValuationBridge.TropPoly.eval_mul` — min-plus multiplicativity
  `eval (P ⊙ Q) = eval P + eval Q`, the *engine* of tropical Bézout.

To keep this file self-contained (and to let it be checked in isolation) we re-state the two
small pieces of vocabulary from that bridge file — the corner-locus predicate
`AttainedAtLeastTwice` and the `TropPoly` structure with its tropical product `TropPoly.mul` —
and then prove the genuinely new **tropical Bézout / factorization** theorems on top of them.

## Main results

* `TropicalBezout.attainedTwice_smul` — **scale invariance of the corner locus**
  (the "valuation → ∞" limit).  Rescaling all weights by a positive constant `t` (as happens
  when the valuation `v` is replaced by `t · v`) does not change the corner locus.  This is the
  precise sense in which the tropical variety is the scale-invariant *limit* of the family of
  amoebas.  It complements `kapranov_easy_direction`, which produces a corner from a single `v`.

* `TropicalBezout.tropRoot_mul_iff` — **the tropical hypersurface of a product is the union of
  the hypersurfaces.**  A point is a tropical root of `P ⊙ Q` iff it is a tropical root of `P` or
  of `Q`.  Combined with `eval_mul` (degrees add), this is the combinatorial core of the tropical
  Bézout theorem: a degree-`d`·degree-`e` intersection decomposes into the right count of pieces.

* `TropicalBezout.tropRootSet_mul` — the set-level restatement `V(P ⊙ Q) = V(P) ∪ V(Q)`.

* `TropicalBezout.range_exp_mul` — **Newton polytopes add (Minkowski sum).**  The exponent
  support of `P ⊙ Q` is the Minkowski sum of the supports of `P` and `Q`.  This is the
  polytope-level shadow of degree additivity underlying Bézout's degree count.

* A boundary case (`tropRoot_mul_subsingleton_right`): multiplying by a single tropical monomial
  adds no roots.
-/

open Finset
open scoped Pointwise

open TropicalBezout

/-! ## §0. Vocabulary inherited from the bridge file (re-stated for self-containment) -/





/-
!-- A single index can never witness `i ≠ j`. -- !--
A one-monomial tropical polynomial has empty corner locus.  Mirrors
`TropicalValuationBridge.attainedTwice_subsingleton`.
-/

/-! ## §1. Scale invariance of the corner locus — the "valuation → ∞" limit -/

/-
!-- Multiplying every weight by a fixed `t > 0` is an order isomorphism on `ℝ`, so
`t * w i ≤ t * w k ↔ w i ≤ w k`; the witnessing indices of the corner are therefore unchanged. -- !--

**Scale invariance (the limiting tropical shape).**  Classically one studies the rescaled
valuations `v_t = t · v` as `t → ∞`.  The corner-locus predicate `AttainedAtLeastTwice` is
invariant under such a positive rescaling, so the tropical variety is genuinely the
scale-independent limit of the family.
-/

/-! ## §2. The general combinatorial lemma: minimizers of a separated sum -/

/-
!-- A pair `(i,k)` minimizes `a i + b k` iff `i` minimizes `a` and `k` minimizes `b`; the
minimizing set is the product of the two minimizing sets, which has ≥ 2 elements iff one factor
does.  Minimizers of `a` and `b` exist by finiteness. -- !--

**Separated-sum corner lemma.**  For a function of the form `(i,k) ↦ a i + b k` on a product of
finite nonempty types, the corner-locus condition holds iff it holds for `a` or for `b`.  This is
the engine behind the tropical factorization theorem below.
-/

/-! ## §3. Tropical hypersurface of a product = union of hypersurfaces -/



/-
!-- Rewrite `termVal (P ⊙ Q)` as the separated sum via `termVal_mul`, then apply
`attainedTwice_add_iff`. -- !--

**Tropical Bézout / factorization (headline).**  A point is a tropical root of the product
`P ⊙ Q` iff it is a tropical root of `P` or of `Q`: the tropical hypersurface of a product is the
union of the hypersurfaces.  This is the combinatorial heart of tropical Bézout, complementing the
degree-additivity engine `TropPoly.eval_mul` from the bridge file.
-/

/-
**Set-level restatement: `V(P ⊙ Q) = V(P) ∪ V(Q)`.**  The tropical zero set of a product is the
union of the tropical zero sets of the factors.
-/

/-! ## §4. Newton polytopes add: the Minkowski-sum law -/

/-
!-- `(P ⊙ Q).exp (i,k) = P.exp i + Q.exp k`, so the range over all pairs is exactly the
pointwise (Minkowski) sum of the two ranges. -- !--

**Newton polytopes add (Minkowski sum).**  The exponent support of the tropical product is the
Minkowski sum of the exponent supports of the factors.  This is the polytope-level expression of
degree additivity (`eval_mul`) and is what makes the Bézout degree count `deg = d · e` work.
-/

/-! ## §5. Boundary case of the headline theorem -/

/-
!-- If `κ` has at most one monomial, `Q` can never contribute a corner, so the union collapses to
`V(P)`; this follows from `tropRoot_mul_iff` together with `attainedTwice_subsingleton`. -- !--

**Boundary case.**  When `Q` is a single tropical monomial (`κ` a subsingleton), it has no corner
locus, so the product's hypersurface is just that of `P`: multiplying by a monomial adds no roots.
-/


open TropicalBezout in
theorem solution{ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (a : ι → ℝ) (b : κ → ℝ) :
    AttainedAtLeastTwice (fun p : ι × κ => a p.1 + b p.2)
      ↔ AttainedAtLeastTwice a ∨ AttainedAtLeastTwice b := by
  constructor;
  · rintro ⟨ p, q, hpq, h₁, h₂ ⟩;
    by_cases h_cases : p.1 = q.1;
    · simp_all +decide [ Prod.ext_iff ];
      exact Or.inr ⟨ p.2, q.2, hpq, fun k => by linarith [ h₁ q.1 k, h₂ q.1 k ], fun k => by linarith [ h₁ q.1 k, h₂ q.1 k ] ⟩;
    · refine' Or.inl ⟨ p.1, q.1, h_cases, fun i => _, fun i => _ ⟩ <;> have := h₁ ( i, p.2 ) <;> have := h₂ ( i, q.2 ) <;> have := h₁ ( i, q.2 ) <;> have := h₂ ( i, p.2 ) <;> norm_num at * <;> linarith;
  · rintro ( h | h );
    · obtain ⟨ i, j, hij, hi, hj ⟩ := h;
      obtain ⟨ k, hk ⟩ := Finset.exists_min_image Finset.univ b ⟨ Classical.arbitrary κ, Finset.mem_univ _ ⟩;
      exact ⟨ ( i, k ), ( j, k ), by aesop, fun p => by linarith [ hi p.1, hj p.1, hk.2 p.2 ( Finset.mem_univ p.2 ) ], fun p => by linarith [ hi p.1, hj p.1, hk.2 p.2 ( Finset.mem_univ p.2 ) ] ⟩;
    · -- Obtain the minimizers of $a$ and $b$.
      obtain ⟨i₀, hi₀⟩ : ∃ i₀, ∀ i, a i₀ ≤ a i := by
        simpa using Finset.exists_min_image Finset.univ a ( Finset.univ_nonempty )
      obtain ⟨k, k', hk⟩ : ∃ k k', k ≠ k' ∧ (∀ l, b k ≤ b l) ∧ (∀ l, b k' ≤ b l) := by
        exact h;
      exact ⟨ ( i₀, k ), ( i₀, k' ), by aesop, fun p => by simpa using add_le_add ( hi₀ p.1 ) ( hk.2.1 p.2 ), fun p => by simpa using add_le_add ( hi₀ p.1 ) ( hk.2.2 p.2 ) ⟩
