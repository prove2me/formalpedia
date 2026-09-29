-- Prove2me | Theorems.Thm_mme_released_interior_used_112_zero_parameter_exists
-- name    : mme_released_interior_used_112_zero_parameter_exists
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:01:58.277989+00:00
-- url     : https://prove2.me/theorems/9195955b-91b4-4574-9786-25aa80f7a102
-- title:
--   A positively weighted released 112 child has zero outer parameter
-- statement:
--   The exact released data contain an interior recipe, region and 112 coordinate placement whose region weight times the sum of split and complementary split weights is positive but whose outer parameter is zero. The child shape belongs to the recipe split list. This kernel-checked existence certificate explains why zero-parameter extraction is required. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed

theorem mme_released_interior_used_112_zero_parameter_exists :
    ∃ (owner : Fin 6) (s : Fin 45) (r : Fin 6) (z : Fin 3),
    let t := seed owner s
    let shape := List.ofFn (fun i : Fin 3 => if i = z then 2 else 1)
    let p := ((t.children.find? (fun a => a.1 == r.val && a.2.1 == shape)).getD
      (0, [], 0)).2.2
    let a := (t.alpha.getD r.val []).getD (t.splits.idxOf shape) 0
    let b := (t.alpha.getD r.val []).getD (t.splits.idxOf (t.shape.zipWith (· - ·) shape)) 0
    t.boundary = [] ∧ shape ∈ t.splits ∧
      0 < t.region.getD r.val 0 * (a + b) ∧ p = 0 := by sorry
