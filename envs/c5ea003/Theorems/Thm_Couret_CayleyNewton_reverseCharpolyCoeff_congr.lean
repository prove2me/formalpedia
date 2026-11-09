-- Prove2me | Theorems.Thm_Couret_CayleyNewton_reverseCharpolyCoeff_congr
-- name    : Couret.CayleyNewton.reverseCharpolyCoeff_congr
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:19:13.953242+00:00
-- url     : https://prove2.me/theorems/17b68867-92cb-461f-ad81-1ccdbb1fd9da
-- title:
--   Equal characteristic polynomials have equal reverse coefficients
-- statement:
--   Let $I$ be a finite index type with decidable equality and let $A,B$ be rational square matrices on $I$. Put $N=|I|$ and define $c_A(k)=[X^{N-k}]\operatorname{charpoly}(A)$ for $k\le N$, and $c_A(k)=0$ for $k>N$; define $c_B$ similarly. If the characteristic polynomials agree, then $$c_A=c_B\qquad\text{as functions }\mathbb N\to\mathbb Q.$$ This includes $k=0$, all indices beyond the dimension, and the empty index type. No Newton recurrence premise is required.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNewton.lean#L33-L40, lines 33–40; source file SHA-256 2a16c18cd916994db6f9967e25da73baa67cd8fa6f444067cba08d9bc99d049c; theorem Couret.CayleyNewton.reverseCharpolyCoeff_congr

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
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

theorem reverseCharpolyCoeff_congr
    {i : Type*} [Fintype i] [DecidableEq i]
    (A B : Matrix i i ℚ) (hp : A.charpoly = B.charpoly) :
    reverseCharpolyCoeff A = reverseCharpolyCoeff B := by sorry


























end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





end Couret.CayleyDoublet
