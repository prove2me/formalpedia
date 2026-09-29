-- Prove2me | Definitions.Def_Logic_TraceDistribution_Functoriality
-- name    : Logic_TraceDistribution_Functoriality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:10:11.963754+00:00
-- url     : https://prove2.me/theorems/b74ff933-7f17-44e2-b92c-4aaf8b3416c5
-- title:
--   Aether Catalog definitions — Logic_TraceDistribution_Functoriality
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TraceDistribution.Functoriality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TraceDistribution/Functoriality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_TraceDistribution_Core
/-
# Functoriality: the trace invariant is a Burnside-ring homomorphism

The trace distribution `{|X^g| : g ∈ G}` is the *unordered* shadow of the finer
pointwise invariant `g ↦ |X^g|`, the **mark** (or permutation-character) function of the
`G`-set `X`.  This file records the structural behaviour of the mark function under the
two operations that make the isomorphism classes of finite `G`-sets into the *Burnside
ring*:

* `fixedCard_prod` — `|(X × Y)^g| = |X^g| · |Y^g|` (multiplication);
* `fixedCard_sum` — `|(X ⊕ Y)^g| = |X^g| + |Y^g|` (addition);
* `fixedCard_of_equivariant_equiv` — invariance under equivariant bijections.

Combining these with the main theorem of `Logic.TraceDistribution.Core` yields a
genuinely two-sided statement (`orbitCount_prod_congr`, `orbitCount_sum_congr`):
*mark equivalence is a congruence for the Burnside-ring operations, and therefore the
whole orbit-count spectrum of a product or a coproduct is determined by the
orbit-count spectra of the factors.*

This is the sense in which Conjecture A is not an isolated identity but a statement
about a ring homomorphism: `X ↦ (g ↦ |X^g|)` from the Burnside ring `A(G)` to the ring
of `ℕ`-valued functions on `G`, and the orbit-count spectrum `k ↦ |X^k / G|` recovers
the image of `X` up to reordering.

## Lab notes (experimental data)

`G = ℤ/2`, `X = G` (regular, marks `(2, 0)`), `Y = Unit` (marks `(1, 1)`):

* `X × Y` has marks `(2·1, 0·1) = (2, 0)`, so `X × Y` is mark-equivalent to `X` —
  consistent with `X × Unit ≅ X`.
* `X ⊕ X` has marks `(4, 0)`; orbit counts `1, 2, 8, 32, …` (`= 4^k / 2` for `k ≥ 1`).
* `X ⊕ Y` has marks `(3, 1)`; orbit counts `1, 2, 5, 14, …` (`= (3^k + 1)/2`).
  Both `X ⊕ X` and `X ⊕ Y` have `4` points and `2` orbits, so the `k = 0` and `k = 1`
  counts agree; separation happens first at `k = 2` (`8` versus `5`), exactly as the
  threshold analysis predicts.
-/

open MulAction Finset

namespace TraceDistribution

variable {G : Type*} [Group G]

/-! ## Fixed points of products and coproducts -/

/-- A pair is fixed exactly when both components are. -/
def fixedByProdEquiv (X Y : Type*) [MulAction G X] [MulAction G Y] (g : G) :
    fixedBy (X × Y) g ≃ (fixedBy X g × fixedBy Y g) where
  toFun p := ⟨⟨p.1.1, by have h := p.2; rw [mem_fixedBy] at h ⊢; exact congrArg Prod.fst h⟩,
              ⟨p.1.2, by have h := p.2; rw [mem_fixedBy] at h ⊢; exact congrArg Prod.snd h⟩⟩
  invFun p := ⟨(p.1.1, p.2.1), by
    rw [mem_fixedBy]
    exact Prod.ext p.1.2 p.2.2⟩
  left_inv p := by ext <;> rfl
  right_inv p := by ext <;> rfl

/-- An element of a disjoint union is fixed exactly when its representative is. -/
def fixedBySumEquiv (X Y : Type*) [MulAction G X] [MulAction G Y] (g : G) :
    fixedBy (X ⊕ Y) g ≃ (fixedBy X g ⊕ fixedBy Y g) where
  toFun := fun p => match p with
    | ⟨Sum.inl x, h⟩ => Sum.inl ⟨x, by
        rw [mem_fixedBy] at h ⊢
        exact Sum.inl_injective h⟩
    | ⟨Sum.inr y, h⟩ => Sum.inr ⟨y, by
        rw [mem_fixedBy] at h ⊢
        exact Sum.inr_injective h⟩
  invFun := fun p => match p with
    | Sum.inl x => ⟨Sum.inl x.1, by rw [mem_fixedBy]; exact congrArg Sum.inl x.2⟩
    | Sum.inr y => ⟨Sum.inr y.1, by rw [mem_fixedBy]; exact congrArg Sum.inr y.2⟩
  left_inv := by rintro ⟨x | y, h⟩ <;> rfl
  right_inv := by rintro (x | y) <;> rfl




/-! ## Mark equivalence is a congruence -/





end TraceDistribution


