-- Prove2me | Theorems.Thm_HypersmoothCounterexamples_theoremA
-- name    : HypersmoothCounterexamples.theoremA
-- status  : Proved
-- author  : @username
-- created : 2026-11-26T02:05:04.480306+00:00
-- url     : https://prove2.me/theorems/b068768b-7f16-48f5-8804-34c8dba1709a
-- title:
--   Theorem A — two commuting continuous maps
-- statement:
--   On the planar array space $x_s(i,j)=s(\tbinom{i+j+1}{2}+j)$, the coordinate shifts are commuting continuous self-maps. Their common-future equivalence relation is not hypersmooth. Each shift has a fiber of cardinality $2^{\aleph_0}$.
-- source:
--   counterexamples-to-hypersmoothness.tex, Theorem A and Section 3. Supplied manuscript SHA-256 03093bc96808d915a59451a3d40499e92916b9ae136e5309dcc9065b86a4a603.

import Definitions.Def_Hypersmooth20261125
import Definitions.Def_QuadrantShifts20261125

set_option autoImplicit false

open HypersmoothCounterexamples

theorem HypersmoothCounterexamples.theoremA :
    Continuous (planarShift (1,0)) ∧ Continuous (planarShift (0,1)) ∧
    Function.Commute (planarShift (1,0)) (planarShift (0,1)) ∧
    ¬ Hypersmooth PlanarRelation ∧
    (∃ y : PlanarArrays,
      Cardinal.mk {x : PlanarArrays // planarShift (1,0) x = y} = Cardinal.continuum) ∧
    (∃ y : PlanarArrays,
      Cardinal.mk {x : PlanarArrays // planarShift (0,1) x = y} = Cardinal.continuum) := by sorry
