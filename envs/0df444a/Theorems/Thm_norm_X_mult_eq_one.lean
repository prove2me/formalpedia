-- Prove2me | Theorems.Thm_norm_X_mult_eq_one
-- name    : norm_X_mult_eq_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T06:26:08.355716+00:00
-- url     : https://prove2.me/theorems/fcddeee9-dc46-4ed2-b163-e0c250cf06fb
-- title:
--   The multiplicative corrector has unit modulus
-- statement:
--   Unconditionally in the phase path $\omega$: $\|X(n, P, \omega)\| = 1$ for every $n$, because the corrector is a finite product of unit-modulus prime factors.

import Mathlib
import Definitions.Def_timepiece_corrector
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

theorem norm_X_mult_eq_one (n P : ℕ) (ω : Ω_infty) : ‖X_mult n P ω‖ = 1 := by sorry
