-- Prove2me | Definitions.Def_Couret_RecohFourierCovarianceBridge_d0f4471a4239
-- name    : Couret_RecohFourierCovarianceBridge_d0f4471a4239
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:24.869721+00:00
-- url     : https://prove2.me/theorems/eca78113-b442-47e7-afe4-d17b362f0e4e
-- title:
--   Character sums of finite supports
-- statement:
--   For an additive abelian group G, an additive character chi : AddChar G ℂ, and a finite subset S of G, recohFourierSum chi S is the complex finite sum of chi(x) over x in S. The empty support has sum zero. The definition needs no finiteness assumption on G and supplies no existence assertion for a character separating two supports.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/60f6d03fdb26a2498e9e856b49f93ad590b99409/research/strobo-2tors-2026-10-12/lean/RecohFourierCovarianceBridge.lean; source file SHA-256 620bdf7b886bd292ce5fc61c0ac3d2d77eeeeea3aa34407de44d4f3ed56befbf

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

/-!
RECOH Fourier covariance bridge — retained copy of the previously certified module.
The existence of a separating character for arbitrary distinct supports remains
an open formalization obligation; do not confuse nonvanishing with separation.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G]





/-- Fourier sum of a finite support. -/
def recohFourierSum (chi : AddChar G ℂ) (S : Finset G) : ℂ :=
  S.sum (fun x => chi x)








end Couret.STROBO2TORS


