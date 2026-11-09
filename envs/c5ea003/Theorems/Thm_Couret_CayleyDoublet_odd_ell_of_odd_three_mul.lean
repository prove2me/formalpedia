-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_odd_ell_of_odd_three_mul
-- name    : Couret.CayleyDoublet.odd_ell_of_odd_three_mul
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:51.301691+00:00
-- url     : https://prove2.me/theorems/72cf5196-8eb3-452f-a04f-6148af334bf5
-- title:
--   An odd triple multiple has an odd factor
-- statement:
--   For natural $\ell$, if $3\ell$ is odd then $\ell$ is odd.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourCanonicalReturn.lean#L165-L170, lines 165–170; source file SHA-256 d42d32ebf171bc2a72aa60523719dbdaaf3f0930bd30560960b5a8d6dae8cfa9; theorem Couret.CayleyDoublet.odd_ell_of_odd_three_mul

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
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

theorem odd_ell_of_odd_three_mul (ell : ℕ)
    (hodd : Odd (3 * ell)) : Odd ell := by sorry






end Couret.CayleyDoublet
