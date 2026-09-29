-- Prove2me | Definitions.Def_Bridges_TropicalStoneWeierstrassMinPlus
-- name    : Bridges_TropicalStoneWeierstrassMinPlus
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:35.710851+00:00
-- url     : https://prove2.me/theorems/ce02aa88-1efa-45ce-9402-f2dde970456c
-- title:
--   Aether Catalog definitions — Bridges_TropicalStoneWeierstrassMinPlus
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalStoneWeierstrassMinPlus`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalStoneWeierstrassMinPlus.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Min-Plus Stone–Weierstrass Theorem

This file formalizes the algebraic tropicalization of EML function algebras via
a tropical Stone–Weierstrass theorem for min-plus semiring-valued continuous maps.

## Main definitions

* `TropMinPlusAdd` — tropical addition: pointwise minimum
* `TropMinPlusMul` — tropical multiplication: pointwise sum
* `tropConst` — tropical scalar constants
* `tropNeg` — order-reversing involution converting min-plus to max-plus

## Main results

* `tropNeg_involutive` — negation is an involution
* `norm_sub_tropNeg_eq` — negation is an isometry: `‖-f - (-g)‖ = ‖f - g‖`
* `tropNeg_tropMinPlusAdd` — negation converts min to max
* `tropNeg_tropMinPlusMul` — negation preserves additive structure (with sign flip)
* `tropSep_iff_neg` — separation is preserved under negation
* `minplus_stone_weierstrass_Icc_via_neg` — min-plus density via negation transport

## Mathematical significance

The decisive bridge is the order-reversing involution `f ↦ -f`, which converts
min-plus structure into max-plus structure:
  `-(min (f x) (g x)) = max (-f x) (-g x)`
  `-(f x + g x) = (-f x) + (-g x)` (note: this is `-((-f) + (-g))` pattern)

This duality means every max-plus density theorem automatically yields a min-plus
density theorem, and vice versa. The min-plus side models "cost-style" observables:
shortest paths, value functions, energy landscapes, and morphological erosions.
-/

noncomputable section

open scoped Topology

/-! ## Type abbreviation -/

/-- The unit interval `[0, 1]` as a compact Hausdorff space. -/
abbrev I01 := Set.Icc (0 : ℝ) 1

/-! ## Min-plus operations on continuous maps -/

/-- Tropical addition: pointwise minimum of two continuous functions. -/
def TropMinPlusAdd (f g : C(I01, ℝ)) : C(I01, ℝ) :=
  ⟨fun x => min (f x) (g x), f.continuous.min g.continuous⟩

/-- Tropical multiplication: pointwise sum of two continuous functions. -/
def TropMinPlusMul (f g : C(I01, ℝ)) : C(I01, ℝ) :=
  ⟨fun x => f x + g x, f.continuous.add g.continuous⟩

/-- Tropical scalar constant. -/
def tropConst (c : ℝ) : C(I01, ℝ) :=
  ContinuousMap.const _ c

/-- Order-reversing involution: the key bridge between min-plus and max-plus. -/
def tropNeg (f : C(I01, ℝ)) : C(I01, ℝ) :=
  ⟨fun x => -f x, f.continuous.neg⟩

/-! ## Basic evaluation lemmas -/





/-! ## Negation is an involution -/



/-! ## Algebraic conversion identities -/




/-! ## Norm invariance under negation -/

/-
**Key transport lemma**: negation is an isometry in the sup norm.
This is the exact technical bridge that converts max-plus approximation
results into min-plus approximation results.
-/

/-! ## Point separation -/

/-- A set of continuous maps separates points if for every pair of
distinct points, some member of the set distinguishes them. -/
def TropSeparatesPoints (A : Set (C(I01, ℝ))) : Prop :=
  ∀ x y : I01, x ≠ y → ∃ f ∈ A, f x ≠ f y

/-
Point separation is preserved under negation: `f` separates `x, y`
iff `-f` separates `x, y`.
-/

/-! ## Uniform approximation -/


/-! ## Main theorem: Min-plus Stone–Weierstrass via negation duality -/

/-
**Min-plus Stone–Weierstrass theorem via negation transport.**

If `A` is a set of continuous functions on `[0,1]` closed under:
  - tropical constants (`x ↦ c` for all `c : ℝ`)
  - tropical addition (pointwise min)
  - tropical multiplication (pointwise sum)

and `A` separates points, then assuming that `tropNeg '' A` is dense
in the max-plus sense, `A` is dense in the sup-norm topology.

This theorem isolates the exact duality mechanism: the negation map
`f ↦ -f` converts min-plus structure into max-plus structure, preserves
the sup norm, and thus transfers density results.
-/

/-! ## General compact Hausdorff version -/

/-
**Min-plus Stone–Weierstrass for general compact Hausdorff spaces.**
Same structure as the interval version, but stated for an arbitrary
compact Hausdorff space `X`.
-/

end


