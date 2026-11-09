-- Prove2me | Theorems.Thm_Couret_CayleyNewton_newtonTraceEquation_eq_at
-- name    : Couret.CayleyNewton.newtonTraceEquation_eq_at
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:30.235276+00:00
-- url     : https://prove2.me/theorems/d8f58bc1-09a9-447d-939e-581c49c2999d
-- title:
--   Uniqueness of the next term of a Newton recurrence
-- statement:
--   For rational sequences $c,u:\mathbb N\to\mathbb Q$, write $N(c,u,k)$ for $u_k+\sum_{j=1}^{k-1}c_j u_{k-j}+kc_k=0$. Let $c,u,v$ be rational sequences and $k>0$ an integer. If $N(c,u,k)$ and $N(c,v,k)$ hold and $u_m=v_m$ for every $0<m<k$, then
--
--   $$u_k=v_k.$$
--
--   There is no condition on the zeroth terms, and the sum is empty for $k=1$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNewton.lean#L53-L76, lines 53–76; source file SHA-256 2a16c18cd916994db6f9967e25da73baa67cd8fa6f444067cba08d9bc99d049c; theorem Couret.CayleyNewton.newtonTraceEquation_eq_at

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

theorem newtonTraceEquation_eq_at
    (c u v : ℕ → ℚ) (k : ℕ) (hk : 0 < k)
    (hu : NewtonTraceEquation c u k)
    (hv : NewtonTraceEquation c v k)
    (hprev : ∀ m : ℕ, 0 < m → m < k → u m = v m) :
    u k = v k := by sorry






















end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





end Couret.CayleyDoublet
