-- Prove2me | solution 1 for EMLDiffEq.airy_no_polynomial_solution
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:56:14.627985+00:00
-- url     : https://prove2.me/submissions/596bc72d-eea1-47a9-b794-3920227fd9d8

import Mathlib
import Definitions.Def_Applications_EML_EMLDifferentialEquations

open Polynomial EMLDiffEq

variable {K : Type*} [Field K]

theorem solution (P : K[X]) (hP : P ≠ 0) :
    derivative (derivative P) ≠ (X : K[X]) * P := by
  intro h
  have hR : ((X : K[X]) * P).natDegree = P.natDegree + 1 := natDegree_X_mul hP
  have hle : (derivative (derivative P)).natDegree ≤ P.natDegree := by
    calc (derivative (derivative P)).natDegree
        ≤ (derivative P).natDegree :=
          (natDegree_derivative_le _).trans (Nat.sub_le _ _)
      _ ≤ P.natDegree :=
          (natDegree_derivative_le _).trans (Nat.sub_le _ _)
  have : (derivative (derivative P)).natDegree = P.natDegree + 1 := by
    rw [h, hR]
  omega
