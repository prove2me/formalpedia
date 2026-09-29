-- Prove2me | Theorems.Thm_Tropical_isMin_productTerms_iff
-- name    : Tropical.isMin_productTerms_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:38:47.356353+00:00
-- url     : https://prove2.me/theorems/73ea9c6f-4a52-492b-8a20-57bdcb3f0965
-- title:
--   A minimal term of either factor gives minimal product terms when paired with
-- statement:
--   A minimal term of either factor gives minimal product terms when paired with
--       a minimal term of the other factor.
--
--   ```lean
--   theorem Tropical.isMin_productTerms_iff(f : I → X → α) (g : J → X → α)
--       (x : X) (i : I) (j : J) :
--       IsMin (productTerms f g) x (i, j) ↔ IsMin f x i ∧ IsMin g x j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/CornerLocusProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/CornerLocusProduct.lean#L32

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

theorem Tropical.isMin_productTerms_iff(f : I → X → α) (g : J → X → α)
    (x : X) (i : I) (j : J) :
    IsMin (productTerms f g) x (i, j) ↔ IsMin f x i ∧ IsMin g x j := by sorry
