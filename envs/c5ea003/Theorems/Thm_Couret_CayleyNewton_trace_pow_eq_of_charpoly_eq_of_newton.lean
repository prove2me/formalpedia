-- Prove2me | Theorems.Thm_Couret_CayleyNewton_trace_pow_eq_of_charpoly_eq_of_newton
-- name    : Couret.CayleyNewton.trace_pow_eq_of_charpoly_eq_of_newton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:31:29.114149+00:00
-- url     : https://prove2.me/theorems/0fb49097-fc37-46f4-883e-9aacef40752c
-- title:
--   Newton recurrences determine all power traces
-- statement:
--   Let $A,B$ be rational square matrices indexed by the same finite type, possibly empty. Suppose their characteristic polynomials agree and each matrix satisfies the specified matrix Newton recurrence. Then $$\operatorname{tr}(A^k)=\operatorname{tr}(B^k)\qquad(k\ge0).$$ Both Newton assumptions remain explicit.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNewton.lean#L284-L309, lines 284–309; source file SHA-256 2a16c18cd916994db6f9967e25da73baa67cd8fa6f444067cba08d9bc99d049c; theorem Couret.CayleyNewton.trace_pow_eq_of_charpoly_eq_of_newton

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyNewton_newtonTraceEquation_unique_positive
import Theorems.Thm_Couret_CayleyNewton_reverseCharpolyCoeff_congr
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

theorem trace_pow_eq_of_charpoly_eq_of_newton
    {i : Type*} [Fintype i] [DecidableEq i]
    (A B : Matrix i i ℚ) (hp : A.charpoly = B.charpoly)
    (hA : SatisfiesMatrixNewton A) (hB : SatisfiesMatrixNewton B) :
    ∀ k : ℕ, Matrix.trace (A ^ k) = Matrix.trace (B ^ k) := by sorry


end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





end Couret.CayleyDoublet
