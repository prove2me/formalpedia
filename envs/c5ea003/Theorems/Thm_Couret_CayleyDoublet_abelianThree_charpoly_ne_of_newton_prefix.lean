-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_charpoly_ne_of_newton_prefix
-- name    : Couret.CayleyDoublet.abelianThree_charpoly_ne_of_newton_prefix
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:40.518457+00:00
-- url     : https://prove2.me/theorems/d1bcc53f-3048-4820-8c6d-ce685dd53f3e
-- title:
--   Finite Newton prefixes give a characteristic-polynomial obstruction
-- statement:
--   Let $G$ be a finite abelian group, $a,d,h\in G$, $\ell>0$, and $Q=G/\langle h\rangle$. Assume $a,h$ generate $G$, $|Q|$ is odd and equals $3\ell$, and the image of $d$ in $Q$ has exact order three. Write $A_+,A_-$ for the rational directed Cayley matrices of supports $\{a,a+d,a+d+h\}$ and $\{a,a-d,a-d+h\}$. Assume $h\ne0$, $2h=0$. For each matrix let $c_j$ be its reversed characteristic coefficient (zero beyond dimension) and $u_j$ its power trace. Assume explicitly for both matrices and every $1\le k\le\ell$ that
--
--   $$u_k+\sum_{j=1}^{k-1}c_j u_{k-j}+kc_k=0.$$
--
--   Then $\chi_{A_+}\ne\chi_{A_-}$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourCanonicalReturn.lean#L195-L245, lines 195–245; source file SHA-256 d42d32ebf171bc2a72aa60523719dbdaaf3f0930bd30560960b5a8d6dae8cfa9; theorem Couret.CayleyDoublet.abelianThree_charpoly_ne_of_newton_prefix

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_canonical_odd_trace_difference
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_trace_eq_before_third
import Theorems.Thm_Couret_CayleyDoublet_quotient_alpha_order_of_pair_generation
import Theorems.Thm_Couret_CayleyNewton_newton_first_coefficient_ne_of_trace_prefix
import Theorems.Thm_Couret_CayleyNewton_reverseCharpolyCoeff_congr
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

theorem abelianThree_charpoly_ne_of_newton_prefix
    (a d h : G) (ell : ℕ)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h)))
    (hell : 0 < ell)
    (hsize : Nat.card (G ⧸ AddSubgroup.zmultiples h) = 3 * ell)
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hS : ∀ k : ℕ, 0 < k → k ≤ ell →
      Couret.CayleyNewton.NewtonTraceEquation
        (Couret.CayleyNewton.reverseCharpolyCoeff
          (abelianCayleyMatrix (AbelianSource a d h)))
        (fun m => Matrix.trace
          (abelianCayleyMatrix (AbelianSource a d h) ^ m)) k)
    (hT : ∀ k : ℕ, 0 < k → k ≤ ell →
      Couret.CayleyNewton.NewtonTraceEquation
        (Couret.CayleyNewton.reverseCharpolyCoeff
          (abelianCayleyMatrix (AbelianTarget a d h)))
        (fun m => Matrix.trace
          (abelianCayleyMatrix (AbelianTarget a d h) ^ m)) k) :
    (abelianCayleyMatrix (AbelianSource a d h)).charpoly ≠
      (abelianCayleyMatrix (AbelianTarget a d h)).charpoly := by sorry


end Couret.CayleyDoublet
