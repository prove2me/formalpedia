-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_noncospectral_odd_of_newton
-- name    : Couret.CayleyDoublet.abelianThree_noncospectral_odd_of_newton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:51.584885+00:00
-- url     : https://prove2.me/theorems/9426e497-36dc-4360-b06c-e3f052f523fd
-- title:
--   Odd generating quotient gives conditional noncospectrality
-- statement:
--   Let $G$ be a finite abelian group, $2h=0$, $h\ne0$, $\operatorname{ord}(d+\langle h\rangle)=3$, $\langle a,h\rangle=G$, and $|G/\langle h\rangle|$ odd. Set $S=\{a,a+d,a+d+h\}$ and $T=\{a,a-d,a-d+h\}$ and let $A_S,A_T$ be their rational directed Cayley adjacency matrices. Assume each matrix satisfies the specified Newton trace equations at every positive index. Then
--
--   $$\operatorname{charpoly}(A_S)\ne\operatorname{charpoly}(A_T).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourThirdFactor.lean#L58-L79, lines 58–79; source file SHA-256 e70e1aee776509b376b41c8a8e2a0e86da60bd4afd69cfc444455445ef314974; theorem Couret.CayleyDoublet.abelianThree_noncospectral_odd_of_newton

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_charpoly_ne_of_newton_prefix
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_exists_canonical_odd_return
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

theorem abelianThree_noncospectral_odd_of_newton
    (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hdorder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h)))
    (hS : SatisfiesMatrixNewton
      (abelianCayleyMatrix (AbelianSource a d h)))
    (hT : SatisfiesMatrixNewton
      (abelianCayleyMatrix (AbelianTarget a d h))) :
    (abelianCayleyMatrix (AbelianSource a d h)).charpoly ≠
      (abelianCayleyMatrix (AbelianTarget a d h)).charpoly := by sorry


end Couret.CayleyDoublet
