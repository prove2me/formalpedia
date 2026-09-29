-- Prove2me | solution 1 for parent_hyp_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:19:17.757826+00:00
-- url     : https://prove2.me/submissions/a2f3d841-98bf-4a9a-acbf-2a13eff6069a

-- Sol generated from Combinatorics/BerggrenTrees/Parent_hyp_lt.lean
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












theorem solution(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 0 < -2*a - 2*b + 3*c := by
  unfold IsPT at hpt
  nlinarith [sq_nonneg (3*c - 2*a - 2*b), sq_nonneg (a - b), mul_pos ha hb]
