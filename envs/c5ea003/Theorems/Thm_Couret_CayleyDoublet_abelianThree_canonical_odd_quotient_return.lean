-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_canonical_odd_quotient_return
-- name    : Couret.CayleyDoublet.abelianThree_canonical_odd_quotient_return
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:31.675125+00:00
-- url     : https://prove2.me/theorems/ff78df08-4110-4c49-91fc-3f1ba7ab9ac0
-- title:
--   The canonical third-period returns to either sign modulo h
-- statement:
--   Let $G$ be a finite abelian group, $a,d,h\in G$, $\ell>0$, and $Q=G/\langle h\rangle$. Assume $a,h$ generate $G$, $|Q|$ is odd and equals $3\ell$, and the image of $d$ in $Q$ has exact order three. Then
--
--   $$\ell a+d\in\langle h\rangle\quad\text{or}\quad\ell a-d\in\langle h\rangle.$$
--
--   This lemma does not require $h$ to be nonzero or killed by two.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourCanonicalReturn.lean#L133-L162, lines 133–162; source file SHA-256 d42d32ebf171bc2a72aa60523719dbdaaf3f0930bd30560960b5a8d6dae8cfa9; theorem Couret.CayleyDoublet.abelianThree_canonical_odd_quotient_return

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyCanonical_canonical_of_odd_cyclic
import Theorems.Thm_Couret_CayleyDoublet_abelian_quotient_zmultiples_generator_of_pair
import Theorems.Thm_Couret_CayleyDoublet_quotient_alpha_order_of_pair_generation
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 -- canonical order-three return in the odd cyclic quotient.
Research source, **UNCOMPILED** with pinned Lean 4.29.1.
No existing certified theorem has been modified.

The first lemma needs only the order of alpha and a bounded coordinate,
and is independent of any representation of a directed graph. The last
lemma translates its canonical witness back to the quotient G/<h>.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyCanonical







end Couret.CayleyCanonical

namespace Couret.CayleyDoublet

open Couret.CayleyCanonical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_canonical_odd_quotient_return
    (a d h : G) (ell : ℕ)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h)))
    (hell : 0 < ell)
    (hsize : Nat.card (G ⧸ AddSubgroup.zmultiples h) = 3 * ell)
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) :
    (ell • a + d ∈ AddSubgroup.zmultiples h ∨
     ell • a - d ∈ AddSubgroup.zmultiples h) := by sorry









end Couret.CayleyDoublet
