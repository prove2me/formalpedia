-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_card_eq_six_quotient_third
-- name    : Couret.CayleyDoublet.abelianThree_card_eq_six_quotient_third
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:30:37.958125+00:00
-- url     : https://prove2.me/theorems/fd889c31-3fd9-4b20-bc51-7c48eb3cdf43
-- title:
--   A nonzero half-turn doubles quotient size
-- statement:
--   Let G be a finite abelian group and h in G with 2h=0 and h≠0. If natural k satisfies |G/<h>|=3k, then $$|G|=6k.$$ No a,d, parity or generation assumptions are needed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourFirstCoeff.lean#L158-L187, lines 158–187; source file SHA-256 e45556611be08e80f77ef2e9b917f78da4477576677474f9c2ab22aad4727fd9; theorem Couret.CayleyDoublet.abelianThree_card_eq_six_quotient_third

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f

/-!
COU-20: the first differing characteristic-polynomial coefficient.

The original spectral equivalence and first-trace certificates are imported
unchanged. We reuse the previously proved finite Newton prefix identities,
the generic single-matrix Newton theorem, and the canonical odd quotient
return. All statements refer to the actual rational directed adjacency
matrices (including their loops).

The numerical absolute-gap formula remains a documented mathematical
corollary, not a claim of formalization in this file.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_card_eq_six_quotient_third
    (h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (k : ℕ)
    (hsize : Nat.card (G ⧸ AddSubgroup.zmultiples h) = 3 * k) :
    Fintype.card G = 6 * k := by sorry





end Couret.CayleyDoublet
