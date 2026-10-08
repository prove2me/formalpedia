-- Prove2me | solution 1 for MovingSofa.inner_normalVector_smul_add_inner_tangentVector_smul
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-05T00:27:47.425089+00:00
-- url     : https://prove2.me/submissions/ce544344-2786-461f-8800-63ee704bdb48

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Definitions.Def_MovingSofa_Geometry_Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
noncomputable section
open MovingSofa


theorem solution (p : Point) (t : Real.Angle) :
    inner ℝ p (normalVector t) • normalVector t +
      inner ℝ p (tangentVector t) • tangentVector t = p := by
  ext i
  fin_cases i <;>
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two] <;>
    nlinarith [congrArg (fun r : ℝ ↦ r * p 0) t.cos_sq_add_sin_sq,
      congrArg (fun r : ℝ ↦ r * p 1) t.cos_sq_add_sin_sq]
