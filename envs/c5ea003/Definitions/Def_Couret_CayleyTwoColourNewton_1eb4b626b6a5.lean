-- Prove2me | Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
-- name    : Couret_CayleyTwoColourNewton_1eb4b626b6a5
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:03:18.974279+00:00
-- url     : https://prove2.me/theorems/af244527-4f02-4079-bbd1-143bc4c13801
-- title:
--   Rational Newton recurrence contracts
-- statement:
--   Defines reversed characteristic-polynomial coefficients, equal to zero past the matrix dimension, and the equation $u_k+\sum_{j=1}^{k-1}c_j u_{k-j}+kc_k=0$. A matrix satisfies the Newton contract when this equation holds for every positive $k$, using its power traces and reversed characteristic coefficients. The contract is an explicit predicate rather than a proof that all matrices satisfy it.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNewton.lean; source file SHA-256 2a16c18cd916994db6f9967e25da73baa67cd8fa6f444067cba08d9bc99d049c

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

/-- Number of rows minus k, interpreted as a coefficient of a monic
characteristic polynomial. Coefficients with k greater than the dimension
are zero by definition; this is essential for high-power Newton recurrences. -/
def reverseCharpolyCoeff {i : Type*} [Fintype i] [DecidableEq i]
    (A : Matrix i i ℚ) (k : ℕ) : ℚ :=
  if k ≤ Fintype.card i then A.charpoly.coeff (Fintype.card i - k) else 0



/-- Newton's recurrence for a power-sum sequence u and monic coefficients c:
u(k) + sum_{1 ≤ j < k} c(j) u(k-j) + k c(k) = 0.

This single uniform statement includes both the low-degree Newton
identities and the high-degree Cayley–Hamilton trace recurrence, provided
c(j) = 0 for j greater than the characteristic-polynomial degree. -/
def NewtonTraceEquation (c u : ℕ → ℚ) (k : ℕ) : Prop :=
  u k +
      (∑ j ∈ Finset.range (k - 1), c (j + 1) * u (k - (j + 1))) +
        (k : ℚ) * c k = 0



















/-- The exact finite-dimensional matrix condition left to certify via
Newton identities (or an equivalent algebraic theorem from Mathlib).
It is an explicit universal recurrence, not a postulated equality of
two distinct matrices' traces. -/
def SatisfiesMatrixNewton
    {i : Type*} [Fintype i] [DecidableEq i] (A : Matrix i i ℚ) : Prop :=
  ∀ k : ℕ, 0 < k →
    NewtonTraceEquation (reverseCharpolyCoeff A)
      (fun m => Matrix.trace (A ^ m)) k



end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





end Couret.CayleyDoublet


