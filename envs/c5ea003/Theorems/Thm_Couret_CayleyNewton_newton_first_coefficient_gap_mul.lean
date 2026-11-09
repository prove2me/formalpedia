-- Prove2me | Theorems.Thm_Couret_CayleyNewton_newton_first_coefficient_gap_mul
-- name    : Couret.CayleyNewton.newton_first_coefficient_gap_mul
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:58:02.234504+00:00
-- url     : https://prove2.me/theorems/9e8f631d-75e6-4600-945e-ba5d1777bc2f
-- title:
--   The first coefficient gap from Newton recurrences
-- statement:
--   For rational sequences $c,u:\mathbb N\to\mathbb Q$, write $N(c,u,k)$ for $u_k+\sum_{j=1}^{k-1}c_j u_{k-j}+kc_k=0$. Let $c,d,u,v$ be rational sequences and $k>0$. Suppose $c_j=d_j$ and $u_j=v_j$ for every $0<j<k$, and suppose $N(c,u,k)$ and $N(d,v,k)$. Then
--
--   $$k(c_k-d_k)=-(u_k-v_k).$$
--
--   No equality at index zero is assumed; the lower-index conditions are vacuous when $k=1$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNewton.lean#L122-L153, lines 122–153; source file SHA-256 2a16c18cd916994db6f9967e25da73baa67cd8fa6f444067cba08d9bc99d049c; theorem Couret.CayleyNewton.newton_first_coefficient_gap_mul

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

theorem newton_first_coefficient_gap_mul
    (c d u v : ℕ → ℚ) (k : ℕ) (hk : 0 < k)
    (hcoeff : ∀ j : ℕ, 0 < j → j < k → c j = d j)
    (htrace : ∀ j : ℕ, 0 < j → j < k → u j = v j)
    (hu : NewtonTraceEquation c u k)
    (hv : NewtonTraceEquation d v k) :
    (k : ℚ) * (c k - d k) = -(u k - v k) := by sorry
















end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





end Couret.CayleyDoublet
