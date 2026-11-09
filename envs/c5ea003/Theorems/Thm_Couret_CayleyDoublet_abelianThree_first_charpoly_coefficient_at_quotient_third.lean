-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_charpoly_coefficient_at_quotient_third
-- name    : Couret.CayleyDoublet.abelianThree_first_charpoly_coefficient_at_quotient_third
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:35.280193+00:00
-- url     : https://prove2.me/theorems/ae10bb8d-fad0-4f59-b501-0f801edae6b7
-- title:
--   The first differing nonleading coefficient
-- statement:
--   Let G be a finite abelian group, a,d,h in G, 2h=0 and h≠0. Put Q=G/<h>, S={a,a+d,a+d+h}, T={a,a-d,a-d+h}, A the rational directed Cayley adjacency matrix of S and B that of T, including any loops. Assume the image of d in Q has additive order exactly three. Assume <a,h>=G and |Q| odd. Set k=|Q|/3 and let c_j(A) denote the reverse characteristic coefficient, namely the coefficient of X^(|G|-j) for j≤|G|. Then $$c_j(A)=c_j(B)\ (0<j<k),\qquad c_k(A)\ne c_k(B).$$ The statement restricts the prefix to positive indices; the leading index zero is not part of that quantified prefix.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourFirstCoeff.lean#L25-L71, lines 25–71; source file SHA-256 e45556611be08e80f77ef2e9b917f78da4477576677474f9c2ab22aad4727fd9; theorem Couret.CayleyDoublet.abelianThree_first_charpoly_coefficient_at_quotient_third

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_trace_difference_at_quotient_third
import Theorems.Thm_Couret_CayleyNewton_newton_coefficient_prefix_eq
import Theorems.Thm_Couret_CayleyNewton_newton_first_coefficient_ne_of_trace_prefix
import Theorems.Thm_Couret_CayleyNewton_satisfiesMatrixNewton
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

theorem abelianThree_first_charpoly_coefficient_at_quotient_third
    (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h))) :
    (∀ j : ℕ, 0 < j →
      j < Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3 →
      reverseCharpolyCoeff (abelianCayleyMatrix (AbelianSource a d h)) j =
        reverseCharpolyCoeff (abelianCayleyMatrix (AbelianTarget a d h)) j) ∧
    reverseCharpolyCoeff (abelianCayleyMatrix (AbelianSource a d h))
      (Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3) ≠
    reverseCharpolyCoeff (abelianCayleyMatrix (AbelianTarget a d h))
      (Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3) := by sorry












end Couret.CayleyDoublet
