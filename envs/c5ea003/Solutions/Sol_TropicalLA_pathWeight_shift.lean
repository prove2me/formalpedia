-- Prove2me | solution 1 for TropicalLA.pathWeight_shift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T09:01:55.737539+00:00
-- url     : https://prove2.me/submissions/9d143e47-9368-4557-a05f-a4afa4275b31

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
open TropicalLA in
theorem solution {ι : Type*} (A : Matrix ι ι ℝ) (p : ℕ → ι) (m : ℕ) :
    pathWeight A p (m + 1) = A (p 0) (p 1) + pathWeight A (fun t => p (t + 1)) m := by
  show ∑ t ∈ Finset.range (m + 1), A (p t) (p (t + 1))
      = A (p 0) (p 1) + ∑ t ∈ Finset.range m, A (p (t + 1)) (p (t + 1 + 1))
  rw [Finset.sum_range_succ']
  ring
