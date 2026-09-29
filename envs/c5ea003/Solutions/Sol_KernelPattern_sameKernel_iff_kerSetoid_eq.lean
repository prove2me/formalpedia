-- Prove2me | solution 1 for KernelPattern.sameKernel_iff_kerSetoid_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T05:52:29.068249+00:00
-- url     : https://prove2.me/submissions/41e84db6-b781-477b-aded-911da7cc607f

import Mathlib
import Definitions.Def_Algebra_KernelPatterns_Core

open KernelPattern

variable {α β : Type*} {n : ℕ}

theorem solution {x : Fin n → α} {y : Fin n → β} :
    SameKernel x y ↔ kerSetoid x = kerSetoid y := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    change (kerSetoid x).r i j ↔ (kerSetoid y).r i j
    rw [h]
