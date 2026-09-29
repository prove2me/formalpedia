-- Prove2me | solution 1 for TropicalLA.IsTropEigen.pathWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:15:02.736763+00:00
-- url     : https://prove2.me/submissions/49bb0854-bf67-4e96-b1fc-9aa0f4620559

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {B : Matrix ι ι ℝ} {lam : ℝ} {w : ι → ℝ}
    (h : IsTropEigen B lam w) (p : ℕ → ι) (m : ℕ) :
    pathWeight B p m + w (p m) ≤ m * lam + w (p 0) := by
  -- one step of the eigen-equation: `B i j + w j ≤ λ + w i`
  have hstep : ∀ i j, B i j + w j ≤ lam + w i := by
    intro i j
    have hi := h i
    unfold tmulVec at hi
    rw [← hi]
    exact Finset.le_sup' (fun j => B i j + w j) (Finset.mem_univ j)
  induction m with
  | zero => simp [pathWeight]
  | succ m ih =>
    have hs := hstep (p m) (p (m + 1))
    have hw : pathWeight B p (m + 1) = pathWeight B p m + B (p m) (p (m + 1)) := by
      simp only [pathWeight, Finset.sum_range_succ]
    rw [hw]
    push_cast
    linarith
