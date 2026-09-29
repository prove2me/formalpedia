-- Prove2me | solution 1 for mme_released_interior_used_112_zero_parameter_exists
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:03:29.603037+00:00
-- url     : https://prove2.me/submissions/e34c3f8a-9e00-47ce-a8d5-47fc60fdc270

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed

theorem solution :
    ∃ (owner : Fin 6) (s : Fin 45) (r : Fin 6) (z : Fin 3),
    let t := seed owner s
    let shape := List.ofFn (fun i : Fin 3 => if i = z then 2 else 1)
    let p := ((t.children.find? (fun a => a.1 == r.val && a.2.1 == shape)).getD
      (0, [], 0)).2.2
    let a := (t.alpha.getD r.val []).getD (t.splits.idxOf shape) 0
    let b := (t.alpha.getD r.val []).getD (t.splits.idxOf (t.shape.zipWith (· - ·) shape)) 0
    t.boundary = [] ∧ shape ∈ t.splits ∧
      0 < t.region.getD r.val 0 * (a + b) ∧ p = 0 := by
  decide +kernel


#print axioms solution
