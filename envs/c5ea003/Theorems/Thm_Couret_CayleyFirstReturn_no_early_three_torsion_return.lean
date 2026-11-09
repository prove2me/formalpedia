-- Prove2me | Theorems.Thm_Couret_CayleyFirstReturn_no_early_three_torsion_return
-- name    : Couret.CayleyFirstReturn.no_early_three_torsion_return
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:17.416637+00:00
-- url     : https://prove2.me/theorems/687daf9e-a283-4646-bd0e-81826751e990
-- title:
--   No early return to a three-torsion element
-- statement:
--   Let $Q$ be any additive group, $\alpha,\delta\in Q$, and $\ell,j\ge0$. If $\operatorname{ord}(\alpha)=3\ell$, $3\delta=0$, and $0<j<\ell$, then $$j\alpha\ne\delta,\qquad j\alpha\ne-\delta.$$
--
--   The strict lower bound excludes the zero iterate; if $\ell\le1$ there is no admissible $j$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourFirstReturn.lean#L24-L47, lines 24–47; source file SHA-256 1dcc5a145d246c6fe4f97e77da583efa74c5bd4607939c25f4fefa9de830b0ef; theorem Couret.CayleyFirstReturn.no_early_three_torsion_return

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
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

theorem no_early_three_torsion_return
    {Q : Type*} [AddGroup Q] (alpha delta : Q) (ell j : ℕ)
    (hord : addOrderOf alpha = 3 * ell)
    (hthree : (3 : ℕ) • delta = 0)
    (hjpos : 0 < j) (hjlt : j < ell) :
    j • alpha ≠ delta ∧ j • alpha ≠ -delta := by sorry


end Couret.CayleyFirstReturn

namespace Couret.CayleyDoublet

open Couret.CayleyFirstReturn

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]







end Couret.CayleyDoublet
