-- Prove2me | Theorems.Thm_Couret_CayleyNewton_newton_first_coefficient_ne_of_trace_prefix
-- name    : Couret.CayleyNewton.newton_first_coefficient_ne_of_trace_prefix
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:18:31.864424+00:00
-- url     : https://prove2.me/theorems/f40589c8-c4ae-4702-8aca-6f1d5ec6c489
-- title:
--   A first Newton trace disagreement forces a coefficient disagreement
-- statement:
--   Let c,d,u,v be functions from the natural numbers to the rationals, and let ell be a positive natural number. For every integer k with 1 ≤ k ≤ ell, suppose both Newton recurrences hold: u(k) + sum over 1 ≤ j < k of c(j)u(k-j) + k c(k) = 0, and v(k) + sum over 1 ≤ j < k of d(j)v(k-j) + k d(k) = 0. Suppose u(k) = v(k) for 1 ≤ k < ell, but u(ell) ≠ v(ell). Then c(ell) ≠ d(ell). At ell = 1 the agreement hypothesis is empty. No condition on values at index zero is required.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNewton.lean#L230-L245, lines 230–245; source file SHA-256 2a16c18cd916994db6f9967e25da73baa67cd8fa6f444067cba08d9bc99d049c; theorem Couret.CayleyNewton.newton_first_coefficient_ne_of_trace_prefix

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyNewton_newton_first_gap_of_trace_prefix
import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d

/-!
COU-20 — rational Newton recurrence research bridge (18 October 2026).

UNCOMPILED PROOF CANDIDATE. Deliberately isolated from certified modules.

This is a substantive intermediate obligation: the all-powers trace
consequence is derived from two explicit, identical Newton recurrences,
NOT from an opaque hypothesis equating the traces. It still remains to
prove that the trace sequence of EVERY rational square matrix satisfies
this exact recurrence from its characteristic polynomial.

Neither the existence of a proof in Mathlib at the pinned commit nor a
Lean 4.29.1 compilation of this file is claimed here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Couret.CayleyNewton

theorem newton_first_coefficient_ne_of_trace_prefix
    (c d u v : ℕ → ℚ) (ell : ℕ) (hell : 0 < ell)
    (hu : ∀ k : ℕ, 0 < k → k ≤ ell → NewtonTraceEquation c u k)
    (hv : ∀ k : ℕ, 0 < k → k ≤ ell → NewtonTraceEquation d v k)
    (htrace : ∀ k : ℕ, 0 < k → k < ell → u k = v k)
    (hdiff : u ell ≠ v ell) :
    c ell ≠ d ell := by sorry








end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





end Couret.CayleyDoublet
