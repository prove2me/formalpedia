-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_canonical_odd_trace_difference
-- name    : Couret.CayleyDoublet.abelianThree_canonical_odd_trace_difference
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:26.05365+00:00
-- url     : https://prove2.me/theorems/5e785c0d-7fce-4cb2-94e6-207e9209aff7
-- title:
--   The first canonical return yields a trace discrepancy
-- statement:
--   Let $G$ be a finite abelian group, $a,d,h\in G$, $\ell>0$, and $Q=G/\langle h\rangle$. Assume $a,h$ generate $G$, $|Q|$ is odd and equals $3\ell$, and the image of $d$ in $Q$ has exact order three. Write $A_+,A_-$ for the rational directed Cayley matrices of supports $\{a,a+d,a+d+h\}$ and $\{a,a-d,a-d+h\}$. Assume also $h\ne0$ and $2h=0$. Then
--
--   $$\operatorname{tr}(A_+^\ell)\ne\operatorname{tr}(A_-^\ell).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourCanonicalReturn.lean#L172-L193, lines 172–193; source file SHA-256 d42d32ebf171bc2a72aa60523719dbdaaf3f0930bd30560960b5a8d6dae8cfa9; theorem Couret.CayleyDoublet.abelianThree_canonical_odd_trace_difference

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_canonical_odd_quotient_return
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_ne_iff
import Theorems.Thm_Couret_CayleyDoublet_odd_ell_of_odd_three_mul
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

theorem abelianThree_canonical_odd_trace_difference
    (a d h : G) (ell : ℕ)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h)))
    (hell : 0 < ell)
    (hsize : Nat.card (G ⧸ AddSubgroup.zmultiples h) = 3 * ell)
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) :
    Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ ell) ≠
      Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ ell) := by sorry




end Couret.CayleyDoublet
