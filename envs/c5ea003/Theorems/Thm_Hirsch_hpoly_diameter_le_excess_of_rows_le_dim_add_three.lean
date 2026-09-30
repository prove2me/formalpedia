-- Prove2me | Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_rows_le_dim_add_three
-- name    : Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T16:09:21.501107+00:00
-- url     : https://prove2.me/theorems/12426807-9602-4014-bd5e-c69fb43f4cb6
-- title:
--   Hirsch bound for H-polyhedra with at most three excess rows
-- statement:
--   Let P be a bounded H-polyhedron in ambient R^d described by n real linear inequalities. If n is at most d+3, then its padded vertex-edge graph diameter is at most n-d (natural subtraction). The description may have redundant inequalities or zero normals, and P may be empty or lower dimensional. No strict feasibility or irredundancy is assumed. In particular, at most two excess describing rows gives diameter at most two. This is the classical small-excess consequence of low-dimensional Hirsch, not a uniform polynomial bound for arbitrary excess.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/2774702c54078cb8efae7bed185ed1b4b93bce5b ; standalone Lean/Axiom gate Actions run 34619780682

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem hpoly_diameter_le_excess_of_rows_le_dim_add_three
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hrows : n ≤ d + 3) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d) := by sorry
end Hirsch
