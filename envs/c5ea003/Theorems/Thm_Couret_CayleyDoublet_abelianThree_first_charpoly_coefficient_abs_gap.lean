-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_charpoly_coefficient_abs_gap
-- name    : Couret.CayleyDoublet.abelianThree_first_charpoly_coefficient_abs_gap
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:58.911006+00:00
-- url     : https://prove2.me/theorems/ebae510a-bcca-47ac-97b5-a1361e682141
-- title:
--   Numerical magnitude of the first coefficient gap
-- statement:
--   Let G be a finite abelian group, a,d,h in G, 2h=0 and h≠0. Put Q=G/<h>, S={a,a+d,a+d+h}, T={a,a-d,a-d+h}, A the rational directed Cayley adjacency matrix of S and B that of T, including any loops. Assume the image of d in Q has additive order exactly three. Assume <a,h>=G and |Q| odd. Put k=|Q|/3. For reverse characteristic coefficients c_j, $$|c_k(A)-c_k(B)|=6\,3^{(k-1)/2}.$$ The exponent uses natural subtraction and division; the premises imply k positive and odd.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourFirstCoeff.lean#L189-L251, lines 189–251; source file SHA-256 e45556611be08e80f77ef2e9b917f78da4477576677474f9c2ab22aad4727fd9; theorem Couret.CayleyDoublet.abelianThree_first_charpoly_coefficient_abs_gap

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_card_eq_six_quotient_third
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_exists_canonical_odd_return
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_charpoly_coefficient_gap_at_quotient_third
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_trace_difference_at_quotient_third
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_gap_abs_of_ne
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

theorem abelianThree_first_charpoly_coefficient_abs_gap
    (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h))) :
    let k := Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3
    |reverseCharpolyCoeff (abelianCayleyMatrix (AbelianSource a d h)) k -
      reverseCharpolyCoeff (abelianCayleyMatrix (AbelianTarget a d h)) k| =
      6 * (3 : ℚ) ^ ((k - 1) / 2) := by sorry



end Couret.CayleyDoublet
