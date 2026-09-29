-- Prove2me | Definitions.Def_mme_released_116_six_region_reconstruction
-- name    : mme_released_116_six_region_reconstruction
-- status  : Definition
-- author  : @Robertboy18
-- created : 2026-09-22T12:58:36.668071+00:00
-- url     : https://prove2.me/theorems/2d3b79fc-12e4-470f-a58a-5fded5534b4c
-- title:
--   Six-region reconstruction of the released (1,1,6) component
-- statement:
--   For owner zero, retain the six region weights, split weights and region-specific square-child parameters of the released (1,1,6) seed. Form the weighted independent child products, encode each pair by its four base-six elementary atoms, and sum contributions with the same atom index. The resulting list is sorted by atom index and has integer scale $d^4$, where $d=10^{12}$.

import Definitions.Def_mme_released_global_joint_counts
import Mathlib.Data.List.Sort

set_option autoImplicit false

namespace MME.Released116
open MoreAsymmetryExactSeed

/-- The first interior component of owner zero in the released seed. -/
def seed : Term := owner0.getD 10 ⟨[], [], [], [], [], [], []⟩

/-- Square child atoms, encoded by two base-six elementary triples. -/
def child (j : ℕ) (shape : List ℕ) : List (ℕ × ℕ) :=
  let d := denominator
  let p := ((seed.children.find? (fun c => c.1 == j && c.2.1 == shape)).getD
    (0, [], 0)).2.2
  if shape = [0,0,4] then [(0,d)]
  else if shape = [0,1,3] then [(6,d/2),(1,d/2)]
  else if shape = [1,0,3] then [(18,d/2),(3,d/2)]
  else if shape = [1,1,2] then [(24,p),(4,p),(19,d/2-p),(9,d/2-p)]
  else []

/-- Region weight times split weight times the two independent child counts.
The four denominator factors give the released joint-count scale. -/
def contributions : List (ℕ × ℕ) :=
  (List.range 6).flatMap fun j =>
    seed.splits.zipIdx |>.flatMap fun (shape, k) =>
      let complement := seed.shape.zipWith (· - ·) shape
      (child j shape).flatMap fun (a, x) =>
        (child j complement).map fun (b, y) =>
          (a + 36*b, seed.region.getD j 0 *
            (seed.alpha.getD j []).getD k 0 * x * y)

/-- Combine repeated atoms and order them by their base-six index. -/
def reconstructed : List (ℕ × ℕ) :=
  ((contributions.map Prod.fst).eraseDups.insertionSort (· ≤ ·)).map fun a =>
    (a, ((contributions.filter (fun p => p.1 == a)).map Prod.snd).sum)

end MME.Released116


