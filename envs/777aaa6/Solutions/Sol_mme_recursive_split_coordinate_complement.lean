-- Prove2me | solution 1 for mme_recursive_split_coordinate_complement
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T09:46:59.043882+00:00
-- url     : https://prove2.me/submissions/3e46c196-b5ea-4a67-a6f9-0918d14a7de1

import Definitions.Def_mme_recursive_split_coordinate_data

open MME MME.RecursiveThinSplit MME.RecursiveYZ

/-- Relabeling the three tensor modes commutes with exchanging the two halves
of an admissible split. -/
theorem solution
    {half : ℕ} (parent : Fin 3 → ℕ)
    (htotal : parent 0 + parent 1 + parent 2 = 2 * half)
    (p : Equiv.Perm (Fin 3)) (c : Split half parent) :
    coordinateEquiv parent p (complement htotal c) =
      complement (coordinate_total htotal p) (coordinateEquiv parent p c) := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rfl


#print axioms solution
