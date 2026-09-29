-- Prove2me | Definitions.Def_Tropical_CornerLocusProduct
-- name    : Tropical_CornerLocusProduct
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:30:01.69715+00:00
-- url     : https://prove2.me/theorems/eb0887dc-282d-45d6-b2fa-f3770f090900
-- title:
--   Aether Catalog definitions — Tropical_CornerLocusProduct
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.CornerLocusProduct`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/CornerLocusProduct.lean by skeleton subtraction
import Mathlib
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Corner loci of min-plus products

A finite tropical polynomial is represented by its finite family of term values.
Its corner locus consists of points where the minimum is attained by at least two
terms.  The theorem below proves, without genericity assumptions, that the corner
locus of a tropical product is the union of the two corner loci.
-/

namespace Tropical

variable {X α I J : Type*}

/-- A term `i` is minimal at `x`. -/
def IsMin [Preorder α] (f : I → X → α) (x : X) (i : I) : Prop :=
  ∀ k, f i x ≤ f k x

/-- The minimum of the finite family of tropical terms is attained at least twice. -/
def IsCorner [Preorder α] (f : I → X → α) (x : X) : Prop :=
  ∃ i j, i ≠ j ∧ IsMin f x i ∧ IsMin f x j

/-- Terms of the min-plus product are pairwise sums of terms. -/
def productTerms [Add α] (f : I → X → α) (g : J → X → α) : I × J → X → α :=
  fun ij x ↦ f ij.1 x + g ij.2 x

section OrderedGroup

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]





end OrderedGroup
end Tropical


