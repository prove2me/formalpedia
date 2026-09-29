-- Prove2me | Theorems.Thm_norm_X_mult_list_eq_one
-- name    : norm_X_mult_list_eq_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T06:25:27.21038+00:00
-- url     : https://prove2.me/theorems/e919e5d2-607e-4f4e-a127-9efd43a01f36
-- title:
--   Corrector factors have unit modulus
-- statement:
--   Each corrector factor $X_p(p, P, \omega)$ has modulus exactly $1$ (it is either the constant $1$ or a unit-circle rotation), hence so does every finite product of them.

import Mathlib
import Definitions.Def_timepiece_corrector
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

theorem norm_X_mult_list_eq_one (P : ℕ) (ω : Ω_infty) (L : List ℕ) :
    ‖(L.map (fun p ↦ X_p p P ω)).prod‖ = 1 := by sorry
