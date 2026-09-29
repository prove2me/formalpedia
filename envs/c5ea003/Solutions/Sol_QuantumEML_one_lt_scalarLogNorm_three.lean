-- Prove2me | solution 1 for QuantumEML.one_lt_scalarLogNorm_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:15:43.465691+00:00
-- url     : https://prove2.me/submissions/b9472121-f624-4497-8a39-3626bf4de9e3

-- Sol generated from NumberTheory/EMLQuantumScalarLog.lean
import Mathlib
import Definitions.Def_NumberTheory_EMLQuantumScalarLog

/-!
# Scalar unitary logarithmic factors for quantum EML activations

We prove the scalar-log unit-circle conjecture from the quantum EML future
questions.  The proof gives the explicit certified interval `[1/2, 3]`: the
norm of `log (1 + t i)` is below one at the left endpoint and above one at the
right endpoint, so continuity supplies an intersection with the unit circle.
-/

noncomputable section

open Complex Set

open QuantumEML










open QuantumEML in
theorem solution: 1 < scalarLogNorm 3 := by
  unfold scalarLogNorm
  have hn : ‖(1 : ℂ) + (3 : ℂ) * I‖ = Real.sqrt 10 := by
    rw [Complex.norm_def]
    congr 1
    norm_num [Complex.normSq]
  have h3sqrt : (3 : ℝ) < Real.sqrt 10 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrt : Real.exp 1 < Real.sqrt 10 := Real.exp_one_lt_three.trans h3sqrt
  have hlog : 1 < Real.log (Real.sqrt 10) := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log (Real.exp_pos 1) (Real.sqrt_pos.2 (by norm_num)) hsqrt
  calc
    1 < |(Complex.log (1 + (3 : ℂ) * I)).re| := by
      rw [Complex.log_re, hn, abs_of_pos]
      · exact hlog
      · exact lt_trans (by norm_num) hlog
    _ ≤ ‖Complex.log (1 + (3 : ℂ) * I)‖ := Complex.abs_re_le_norm _
