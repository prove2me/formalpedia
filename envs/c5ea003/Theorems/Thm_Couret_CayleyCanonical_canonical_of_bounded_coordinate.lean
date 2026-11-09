-- Prove2me | Theorems.Thm_Couret_CayleyCanonical_canonical_of_bounded_coordinate
-- name    : Couret.CayleyCanonical.canonical_of_bounded_coordinate
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:41:26.163479+00:00
-- url     : https://prove2.me/theorems/f55f417c-d18e-4faa-879a-5b7eb577b80a
-- title:
--   Canonical third-period multiple from a natural coordinate
-- statement:
--   Let $Q$ be an abelian group, $\alpha,\delta\in Q$ and $\ell>0$ natural with $\operatorname{ord}(\alpha)=3\ell$, $3\delta=0$ and $\delta\ne0$. Let $k<3\ell$ satisfy $k\alpha=\delta$. Then
--
--   $$\ell\alpha=\delta\quad\text{or}\quad\ell\alpha=-\delta.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourCanonicalReturn.lean#L18-L63, lines 18–63; source file SHA-256 d42d32ebf171bc2a72aa60523719dbdaaf3f0930bd30560960b5a8d6dae8cfa9; theorem Couret.CayleyCanonical.canonical_of_bounded_coordinate

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

theorem canonical_of_bounded_coordinate
    {Q : Type*} [AddCommGroup Q]
    (alpha delta : Q) (ell k : ℕ)
    (hell : 0 < ell)
    (hord : addOrderOf alpha = 3 * ell)
    (hk : k < 3 * ell)
    (hcoordinate : k • alpha = delta)
    (hthree : (3 : ℕ) • delta = 0)
    (hne : delta ≠ 0) :
    ell • alpha = delta ∨ ell • alpha = -delta := by sorry






end Couret.CayleyCanonical

namespace Couret.CayleyDoublet

open Couret.CayleyCanonical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]










end Couret.CayleyDoublet
