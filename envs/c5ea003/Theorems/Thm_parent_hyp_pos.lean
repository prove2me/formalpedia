-- Prove2me | Theorems.Thm_parent_hyp_pos
-- name    : parent_hyp_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:14:50.145472+00:00
-- url     : https://prove2.me/theorems/cd450a95-c536-4777-a209-5039bc6ac2a2
-- title:
--   The parent hypotenuse 3c - 2(a+b) is positive for any PPT with a,b,c > 0.
-- statement:
--   The parent hypotenuse 3c - 2(a+b) is positive for any PPT with a,b,c > 0.
--
--   ```lean
--   theorem parent_hyp_pos(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
--       (hpt : IsPT a b c) : 0 < -2*a - 2*b + 3*c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/BerggrenTrees/Parent_hyp_lt.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/BerggrenTrees/Parent_hyp_lt.lean#L37

-- Thm stub generated from Combinatorics/BerggrenTrees/Parent_hyp_lt.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3

The three inverse Barning–Hall matrices `invB1`, `invB2`, `invB3`, the predicate
`IsPT`, and the auxiliary positivity lemmas used by `parent_exists` were missing
from the catalog; they are supplied here so that the file elaborates.
-/

theorem parent_hyp_pos(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 0 < -2*a - 2*b + 3*c := by sorry
