-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_quotient_alpha_order_of_pair_generation
-- name    : Couret.CayleyDoublet.quotient_alpha_order_of_pair_generation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:53:43.287355+00:00
-- url     : https://prove2.me/theorems/38c32ab0-d345-4076-85ba-65899f9cc738
-- title:
--   Order of the generator in a two-generator quotient
-- statement:
--   Let $G$ be a finite abelian group. If $a,h\in G$ generate $G$, then
--
--   $$\operatorname{ord}(a+\langle h\rangle)=|G/\langle h\rangle|.$$
--
--   This includes the trivial quotient, where the order is one.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourFirstReturn.lean#L57-L76, lines 57–76; source file SHA-256 1dcc5a145d246c6fe4f97e77da583efa74c5bd4607939c25f4fefa9de830b0ef; theorem Couret.CayleyDoublet.quotient_alpha_order_of_pair_generation

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelian_quotient_zmultiples_generator_of_pair
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

theorem quotient_alpha_order_of_pair_generation (a h : G)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤) :
    addOrderOf (a : G ⧸ AddSubgroup.zmultiples h) =
      Nat.card (G ⧸ AddSubgroup.zmultiples h) := by sorry






end Couret.CayleyDoublet
