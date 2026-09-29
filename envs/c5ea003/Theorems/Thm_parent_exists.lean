-- Prove2me | Theorems.Thm_parent_exists
-- name    : parent_exists
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:34:59.120953+00:00
-- url     : https://prove2.me/theorems/fae0c603-1ec4-4c97-8fb1-ba38d3b11831
-- title:
--   [Section: # CatalogBuild.Shared.Parent_hyp_lt
-- statement:
--   [Section: # CatalogBuild.Shared.Parent_hyp_lt
--   Auto-generated from theorem catalog database.
--   Domain: Pythagorean/Berggren
--   Declarations: 3]
--
--   ```lean
--   theorem parent_exists(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
--       (hpt : IsPT a b c) (hc5 : c > 5) (hprim : Int.gcd a b = 1) :
--       (0 < (invB1 a b c).1 ∧ 0 < (invB1 a b c).2.1 ∧ 0 < (invB1 a b c).2.2) ∨
--       (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) ∨
--       (0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BerggrenTrees/Parent_hyp_lt.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BerggrenTrees/Parent_hyp_lt.lean#L73

-- Thm stub generated from Bridges/BerggrenTrees/Parent_hyp_lt.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenTrees_Parent_hyp_lt

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

/-! ## Reconstructed definitions

`IsPT` is the Pythagorean relation, and `invB1`, `invB2`, `invB3` are the three
inverse Berggren maps (the parent maps of the Berggren ternary tree), i.e. the
inverses of the matrices `[[1,-2,2],[2,-1,2],[2,-2,3]]`, `[[1,2,2],[2,1,2],[2,2,3]]`
and `[[-1,2,2],[-2,1,2],[-2,2,3]]`. -/

theorem parent_exists(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (hc5 : c > 5) (hprim : Int.gcd a b = 1) :
    (0 < (invB1 a b c).1 ∧ 0 < (invB1 a b c).2.1 ∧ 0 < (invB1 a b c).2.2) ∨
    (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) ∨
    (0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2) := by sorry
