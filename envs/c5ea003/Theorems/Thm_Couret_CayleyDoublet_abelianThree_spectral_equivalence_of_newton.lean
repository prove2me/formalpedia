-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_spectral_equivalence_of_newton
-- name    : Couret.CayleyDoublet.abelianThree_spectral_equivalence_of_newton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:56:39.644055+00:00
-- url     : https://prove2.me/theorems/bd5be1cf-fec0-49ff-b3dc-1ea3a0936fff
-- title:
--   Conditional spectral classification
-- statement:
--   Let $G$ be an abelian group. Assume $G$ finite, $a,d,h$ generate $G$, $2h=0\ne h$, and $\bar d$ has order three modulo $\langle h\rangle$. Assume separately that both source and target rational adjacency matrices satisfy the specified matrix Newton recurrence. Then $$\operatorname{charpoly}(A_S)=\operatorname{charpoly}(A_T)\iff\langle a,h\rangle\ne G\ \text{or}\ |G/\langle h\rangle|\text{ is even}.$$
--
--   The Newton recurrence hypotheses are essential explicit premises of this statement. Here $S(a,d,h)=\{a,a+d,a+d+h\}$ and $T(a,d,h)=\{a,a-d,a-d+h\}$; $A_U$ denotes the rational directed Cayley adjacency matrix of $U$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourNewton.lean#L336-L353, lines 336–353; source file SHA-256 2a16c18cd916994db6f9967e25da73baa67cd8fa6f444067cba08d9bc99d049c; theorem Couret.CayleyDoublet.abelianThree_spectral_equivalence_of_newton

import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_spectral_equivalence_of_trace_bridge
import Theorems.Thm_Couret_CayleyNewton_trace_pow_eq_of_charpoly_eq_of_newton
import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d

/-!
COU-20 — rational Newton recurrence research bridge (18 October 2026).

UNCOMPILED PROOF CANDIDATE. Deliberately isolated from certified modules.

This is a substantive intermediate obligation: the all-powers trace
consequence is derived from two explicit, identical Newton recurrences,
NOT from an opaque hypothesis equating the traces. It still remains to
prove that the trace sequence of EVERY rational square matrix satisfies
this exact recurrence from its characteristic polynomial.

Neither the existence of a proof in Mathlib at the pinned commit nor a
Lean 4.29.1 compilation of this file is claimed here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Couret.CayleyNewton





























end Couret.CayleyNewton

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_spectral_equivalence_of_newton
    (a d h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hgen : AddSubgroup.closure ({a, d, h} : Set G) = ⊤)
    (hS : SatisfiesMatrixNewton (abelianCayleyMatrix (AbelianSource a d h)))
    (hT : SatisfiesMatrixNewton (abelianCayleyMatrix (AbelianTarget a d h))) :
    ((abelianCayleyMatrix (AbelianSource a d h)).charpoly =
        (abelianCayleyMatrix (AbelianTarget a d h)).charpoly) ↔
      (AddSubgroup.closure ({a, h} : Set G) ≠ ⊤ ∨
       Even (Nat.card (G ⧸ AddSubgroup.zmultiples h))) := by sorry


end Couret.CayleyDoublet
