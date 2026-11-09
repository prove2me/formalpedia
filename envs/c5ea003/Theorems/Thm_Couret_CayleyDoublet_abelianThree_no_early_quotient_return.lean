-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_no_early_quotient_return
-- name    : Couret.CayleyDoublet.abelianThree_no_early_quotient_return
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:38.52235+00:00
-- url     : https://prove2.me/theorems/643f90ce-8de5-4f29-b82d-4741462e6805
-- title:
--   No quotient return before one third of the period
-- statement:
--   Let $G$ be a finite abelian group. Let $a,d,h\in G$ and $\ell,j\in\mathbb N$. Suppose $\operatorname{ord}(a+\langle h\rangle)=3\ell$, $\operatorname{ord}(d+\langle h\rangle)=3$, and $0<j<\ell$. Then
--
--   $$ja+d\notin\langle h\rangle,\qquad ja-d\notin\langle h\rangle.$$
--
--   This excludes both signs of an early third-torsion return.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourFirstReturn.lean#L78-L110, lines 78–110; source file SHA-256 1dcc5a145d246c6fe4f97e77da583efa74c5bd4607939c25f4fefa9de830b0ef; theorem Couret.CayleyDoublet.abelianThree_no_early_quotient_return

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyFirstReturn_no_early_three_torsion_return
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

theorem abelianThree_no_early_quotient_return (a d h : G) (ell j : ℕ)
    (hord : addOrderOf (a : G ⧸ AddSubgroup.zmultiples h) = 3 * ell)
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hjpos : 0 < j) (hjlt : j < ell) :
    ¬ (j • a + d ∈ AddSubgroup.zmultiples h ∨
       j • a - d ∈ AddSubgroup.zmultiples h) := by sorry




end Couret.CayleyDoublet
