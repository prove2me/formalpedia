-- Prove2me | Theorems.Thm_Tropical_isCorner_productTerms_iff
-- name    : Tropical.isCorner_productTerms_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:38:50.625511+00:00
-- url     : https://prove2.me/theorems/09dd9527-1fa2-4133-bfc4-63c4ffe16086
-- title:
--   Fundamental min-plus factorization law: the corner locus of a tropical
-- statement:
--   Fundamental min-plus factorization law: the corner locus of a tropical
--   product is exactly the union of the corner loci of its factors.
--
--   ```lean
--   theorem Tropical.isCorner_productTerms_iff    (f : I → X → α) (g : J → X → α) (x : X)
--       (hf : ∃ i, IsMin f x i) (hg : ∃ j, IsMin g x j) :
--       IsCorner (productTerms f g) x ↔ IsCorner f x ∨ IsCorner g x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/CornerLocusProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/CornerLocusProduct.lean#L52

-- Thm stub generated from Tropical/CornerLocusProduct.lean
import Mathlib
import Definitions.Def_Tropical_CornerLocusProduct
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Corner loci of min-plus products

A finite tropical polynomial is represented by its finite family of term values.
Its corner locus consists of points where the minimum is attained by at least two
terms.  The theorem below proves, without genericity assumptions, that the corner
locus of a tropical product is the union of the two corner loci.
-/

open Tropical

variable {X α I J : Type*}





variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

theorem Tropical.isCorner_productTerms_iff    (f : I → X → α) (g : J → X → α) (x : X)
    (hf : ∃ i, IsMin f x i) (hg : ∃ j, IsMin g x j) :
    IsCorner (productTerms f g) x ↔ IsCorner f x ∨ IsCorner g x := by sorry
