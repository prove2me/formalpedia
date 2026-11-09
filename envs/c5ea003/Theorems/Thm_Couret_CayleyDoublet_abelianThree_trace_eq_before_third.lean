-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_trace_eq_before_third
-- name    : Couret.CayleyDoublet.abelianThree_trace_eq_before_third
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:27:17.206288+00:00
-- url     : https://prove2.me/theorems/f77a38a7-7b8b-4bc1-a510-1eb35b1e6807
-- title:
--   Traces agree before the third-period threshold
-- statement:
--   Let $G$ be an abelian group. Assume $G$ finite, $2h=0\ne h$, and the images of $d,a$ in $G/\langle h\rangle$ have orders $3,3\ell$, respectively. For natural numbers $j,\ell$ with $j<\ell$, $$\operatorname{tr}(A_S^j)=\operatorname{tr}(A_T^j).$$
--
--   The degree $j=0$ is included; there is no assertion at $j=\ell$. Here $S(a,d,h)=\{a,a+d,a+d+h\}$ and $T(a,d,h)=\{a,a-d,a-d+h\}$; $A_U$ denotes the rational directed Cayley adjacency matrix of $U$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourFirstReturn.lean#L112-L132, lines 112–132; source file SHA-256 1dcc5a145d246c6fe4f97e77da583efa74c5bd4607939c25f4fefa9de830b0ef; theorem Couret.CayleyDoublet.abelianThree_trace_eq_before_third

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_even_trace_eq_of_square
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_no_early_quotient_return
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_ne_iff
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 — separation before the canonical third-period (18 October 2026).

RESEARCH PROOF CANDIDATES — NOT YET COMPILED.

This module separates two logically different tasks:
(1) if the image of a has order 3*ell and 3*delta=0, then no positive
    j<ell can reach +delta or -delta; this needs no cyclic classification;
(2) the quotient application transfers this fact into equality of the
    directed adjacency-matrix traces at EVERY degree strictly below ell.

It does NOT prove that ell*a is +delta or -delta: the canonical RETURN
theorem is still a distinct open Lean obligation. It also does NOT prove
the universal Newton identity needed for characteristic coefficients.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyFirstReturn



end Couret.CayleyFirstReturn

namespace Couret.CayleyDoublet

open Couret.CayleyFirstReturn

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_trace_eq_before_third (a d h : G) (ell j : ℕ)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hord : addOrderOf (a : G ⧸ AddSubgroup.zmultiples h) = 3 * ell)
    (hjlt : j < ell) :
    Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ j) =
      Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ j) := by sorry


end Couret.CayleyDoublet
