-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_PluckerFourPoint
-- name    : Bridges_TropicalAlgebra_PluckerFourPoint
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:29.92416+00:00
-- url     : https://prove2.me/theorems/b8e1ea64-08a9-41b0-b294-ac328d31c4b2
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_PluckerFourPoint
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.PluckerFourPoint`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/PluckerFourPoint.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.

# Tropical Plücker Relations and the Four-Point Condition

This file establishes the formal bridge between tropical Grassmannian algebra
and tree-metric combinatorics by proving that the tropical Plücker relation
on quadruples is equivalent to the four-point condition on distance matrices.

## Mathematical context

Given a symmetric function `d : α → α → ℝ`, define three pair-sums for any
quadruple `(a, b, c, e)`:
  - `s₁ = d a b + d c e`
  - `s₂ = d a c + d b e`
  - `s₃ = d a e + d b c`

The **tropical Plücker relation** states that each `sᵢ` is at most the
maximum of the other two. Equivalently, the minimum of the three sums is
attained at least twice.

The **four-point condition** states that whenever one sum is the smallest,
the other two are equal. Equivalently, the maximum of the three sums is
attained at least twice.

These two conditions are equivalent for symmetric `d`, and this equivalence
is the algebraic core of the correspondence between the tropical Grassmannian
`Trop(Gr(2,n))`, the Dressian, and finite tree metrics.

## Main results

* `tropical_plucker_equiv_four_point` — the tropical Plücker relation on all
  quadruples is equivalent to the four-point condition, assuming symmetry.
* `tropical_plucker_metric_implies_four_point` — the version with full metric
  axioms (symmetry, zero diagonal, nonnegativity, triangle inequality) implying
  the four-point condition.

## References

* Speyer, D. and Sturmfels, B. "The tropical Grassmannian" (2004)
* Dress, A. and Terhalle, W. "The tree all-or-nothing principle" (1996)
* Buneman, P. "The recovery of trees from measures of dissimilarity" (1971)
-/


open scoped Matrix

/-! ## Definitions -/

/-- The four-point condition: for every four indices, the largest two of the three
pairwise distance sums are equal. Equivalently, whenever one sum is the minimum,
the other two are equal. This characterizes tree metrics (Buneman, 1971). -/
def FourPointCond {α : Type*} (d : α → α → ℝ) : Prop :=
  ∀ a b c e : α,
    let s1 := d a b + d c e
    let s2 := d a c + d b e
    let s3 := d a e + d b c
    ((s1 ≤ s2 ∧ s1 ≤ s3) → s2 = s3) ∧
    ((s2 ≤ s1 ∧ s2 ≤ s3) → s1 = s3) ∧
    ((s3 ≤ s1 ∧ s3 ≤ s2) → s1 = s2)

/-- The tropical Plücker relation: for every quadruple, each pair-sum is at most
the maximum of the other two. Equivalently, the minimum of the three pair-sums
is attained at least twice. -/
def TropicalPlucker {α : Type*} (d : α → α → ℝ) : Prop :=
  ∀ a b c e : α,
    d a b + d c e ≤ max (d a c + d b e) (d a e + d b c)

/-! ## Abstract three-number lemma

The core algebraic fact: three real numbers `x, y, z` satisfy
"each ≤ max of the other two" if and only if "whenever one is the min,
the other two are equal". -/

/-
If each of three reals is ≤ the max of the other two, then whenever one is
the minimum, the other two are equal.
-/

/-
Conversely, the four-point property on three reals implies each is ≤ the max
of the other two.
-/

/-! ## Permutation lemmas for the Plücker inequality

The tropical Plücker condition gives `s₁ ≤ max s₂ s₃` directly.
Using symmetry of `d`, we derive the other two inequalities by
permuting the arguments. -/

/-
From the Plücker inequality `d a b + d c e ≤ max (d a c + d b e) (d a e + d b c)`
applied to `(a, c, b, e)` and using symmetry, we get
`d a c + d b e ≤ max (d a b + d c e) (d a e + d b c)`.
-/

/-
From the Plücker inequality applied to `(a, e, b, c)` and using symmetry,
we get `d a e + d b c ≤ max (d a b + d c e) (d a c + d b e)`.
-/

/-! ## Main equivalence theorem -/

/-
**Tropical Plücker ↔ Four-Point Condition.**
For a symmetric function `d : α → α → ℝ`, the tropical Plücker relation
is equivalent to the four-point condition. This is the algebraic core of the
correspondence between the tropical Grassmannian and tree metrics.
-/

/-! ## The metric version -/


/-! ## Compatibility with Matrix-based FourPointCondition -/


/-! ## The full equivalence in the metric setting -/


