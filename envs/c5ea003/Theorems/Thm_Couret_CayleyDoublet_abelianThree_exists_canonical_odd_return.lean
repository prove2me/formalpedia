-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_exists_canonical_odd_return
-- name    : Couret.CayleyDoublet.abelianThree_exists_canonical_odd_return
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:11:33.740596+00:00
-- url     : https://prove2.me/theorems/27d6de9f-cf1d-44b8-896e-5320dfa10b96
-- title:
--   Existence of the canonical odd quotient return
-- statement:
--   Let $G$ be a finite abelian group and $a,d,h\in G$. Suppose $\langle a,h\rangle=G$, $|G/\langle h\rangle|$ is odd, and $d+\langle h\rangle$ has exact order three. Then
--
--   $$\exists\ell>0:\quad\ell\text{ odd},\quad|G/\langle h\rangle|=3\ell,\quad \ell a+d\in\langle h\rangle\text{ or }\ell a-d\in\langle h\rangle.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourThirdFactor.lean#L41-L56, lines 41–56; source file SHA-256 e70e1aee776509b376b41c8a8e2a0e86da60bd4afd69cfc444455445ef314974; theorem Couret.CayleyDoublet.abelianThree_exists_canonical_odd_return

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_canonical_odd_quotient_return
import Theorems.Thm_Couret_CayleyDoublet_odd_ell_of_odd_three_mul
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20, research-only quotient factor / first-coefficient assembly.
UNCOMPILED candidate (Lean 4.29.1). The first bridge eliminates explicit
arithmetic parameters ell, hell and hsize. The second derives a
noncospectrality theorem under finite-dimensional Newton recurrences.
-/
set_option autoImplicit false
noncomputable section

namespace Couret.CayleyThirdFactor



end Couret.CayleyThirdFactor

namespace Couret.CayleyDoublet

open Couret.CayleyThirdFactor
open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_exists_canonical_odd_return
    (a d h : G)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h)))
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) :
    ∃ ell : ℕ, 0 < ell ∧ Odd ell ∧
      Nat.card (G ⧸ AddSubgroup.zmultiples h) = 3 * ell ∧
      (ell • a + d ∈ AddSubgroup.zmultiples h ∨
       ell • a - d ∈ AddSubgroup.zmultiples h) := by sorry




end Couret.CayleyDoublet
