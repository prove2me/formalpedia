-- Prove2me | solution 1 for KernelPattern.SameKernel.symm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T05:52:24.431287+00:00
-- url     : https://prove2.me/submissions/0ab0433f-00c6-4c63-96ba-552418427133

import Mathlib
import Definitions.Def_Algebra_KernelPatterns_Core

open KernelPattern

variable {α β : Type*} {n : ℕ}

theorem solution {x : Fin n → α} {y : Fin n → β} (h : SameKernel x y) :
    SameKernel y x := by
  intro i j
  exact (h i j).symm
