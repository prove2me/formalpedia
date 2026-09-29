-- Prove2me | solution 1 for Erdos180.symplecticAutomorphism_disjoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:13:59.016615+00:00
-- url     : https://prove2.me/submissions/d281d878-54e8-46bb-ae3d-b4a2e5dc8c1b

import Definitions.Def_erdos180_core4
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    (e : SymplecticAutomorphism K)
    (L M : SymplecticLine K) :
    Disjoint (symplecticAutomorphismLine K e L).1
        (symplecticAutomorphismLine K e M).1 ↔
      Disjoint L.1 M.1 := by
  change
    Disjoint (L.1.map e.toLinearEquiv.toLinearMap)
        (M.1.map e.toLinearEquiv.toLinearMap) ↔
      Disjoint L.1 M.1
  rw [disjoint_iff,
    ← Submodule.map_inf e.toLinearEquiv.toLinearMap
      e.toLinearEquiv.injective,
    Submodule.map_eq_bot_iff,
    ← disjoint_iff]
