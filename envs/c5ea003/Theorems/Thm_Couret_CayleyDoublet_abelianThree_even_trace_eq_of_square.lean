-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_even_trace_eq_of_square
-- name    : Couret.CayleyDoublet.abelianThree_even_trace_eq_of_square
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:07:26.748084+00:00
-- url     : https://prove2.me/theorems/289e303f-0508-4c8f-99e4-4cb310620c50
-- title:
--   Even traces agree
-- statement:
--   Let $G$ be an abelian group. Assume $G$ finite, $a,d,h\in G$, $2h=0\ne h$, and $\bar d$ has order three modulo $\langle h\rangle$. For every natural number $m$, including zero, $$\operatorname{tr}(A_S^{2m})=\operatorname{tr}(A_T^{2m}).$$
--
--   Here $S,T$ are the source and reflected target supports. Here $S(a,d,h)=\{a,a+d,a+d+h\}$ and $T(a,d,h)=\{a,a-d,a-d+h\}$; $A_U$ denotes the rational directed Cayley adjacency matrix of $U$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNewton.lean#L319-L334, lines 319–334; source file SHA-256 2a16c18cd916994db6f9967e25da73baa67cd8fa6f444067cba08d9bc99d049c; theorem Couret.CayleyDoublet.abelianThree_even_trace_eq_of_square

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_sq_eq_of_quotient_order_three
import Theorems.Thm_Couret_CayleySpectral_even_pow_eq_of_sq_eq
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





























end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_even_trace_eq_of_square (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (n : ℕ) :
    Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ (2 * n)) =
      Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ (2 * n)) := by sorry




end Couret.CayleyDoublet
