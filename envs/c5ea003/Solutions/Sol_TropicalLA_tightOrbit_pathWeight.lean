-- Prove2me | solution 1 for TropicalLA.tightOrbit_pathWeight
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T06:55:16.019431+00:00
-- url     : https://prove2.me/submissions/f7d127b6-312f-452a-bd07-067e8f0be068

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalReducible
open TropicalLA in
theorem solution {ι : Type*} {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ} {v : ι → ℝ} {f : ι → ι}
    (hf : ∀ i, finPart A i (f i) = lam + v i - v (f i)) (x : ι) (m : ℕ) :
    pathWeight (finPart A) (fun t => f^[t] x) m = m * lam + v x - v (f^[m] x) := by
  -- each tight step contributes `λ + v(fᵗ x) - v(fᵗ⁺¹ x)`: the sum telescopes
  induction m with
  | zero => simp [pathWeight]
  | succ m ih =>
    have hw : pathWeight (finPart A) (fun t => f^[t] x) (m + 1)
        = pathWeight (finPart A) (fun t => f^[t] x) m + finPart A (f^[m] x) (f^[m + 1] x) := by
      simp only [pathWeight, Finset.sum_range_succ]
    rw [hw, ih, Function.iterate_succ_apply', hf]
    push_cast
    ring
