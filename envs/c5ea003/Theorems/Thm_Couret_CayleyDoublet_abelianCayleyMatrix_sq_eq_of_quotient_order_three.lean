-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_sq_eq_of_quotient_order_three
-- name    : Couret.CayleyDoublet.abelianCayleyMatrix_sq_eq_of_quotient_order_three
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:02:19.47372+00:00
-- url     : https://prove2.me/theorems/d3b93cfe-0f27-47de-bf34-04115740abaf
-- title:
--   Equal adjacency squares for the exceptional triple pair
-- statement:
--   Let $G$ be a finite abelian group. Suppose $a,d,h\in G$, $2h=0$, $h\ne0$, and the image of $d$ in $G/\langle h\rangle$ has exact order three. Write $S=\{a,a+d,a+d+h\}$ and $T=\{a,a-d,a-d+h\}$, and let $A_U(x,y)=1$ if $y-x\in U$ and $0$ otherwise, with rational entries. Then
--
--   $$A_S^2=A_T^2.$$
--
--   This identifies the two-step walk counts of the directed Cayley graphs.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L509-L529, lines 509–529; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleyDoublet.abelianCayleyMatrix_sq_eq_of_quotient_order_three

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianOrderedSquare_source_target
import Theorems.Thm_Couret_CayleyDoublet_abelianSixSeparations_of_double_ne
import Theorems.Thm_Couret_CayleyDoublet_abelian_quotient_addOrderOf_three_iff
import Theorems.Thm_Couret_CayleyDoublet_no_cross_collision_of_order_three
import Definitions.Def_Couret_CayleyTwoColourAbelian_32e780a833c0

/-!
COU-20 — finite directed spectral bridge (17 October 2026).

This file connects finite-support convolution to the actual rational adjacency
matrices, proves cospectrality for a supplied additive parity and for the
already certified nongeneration branch, and proves exact odd-power and trace
difference formulas. Translation sums are identified with Finset adjacency
only after distinctness has been derived from the exact quotient order.

The construction of parity from quotient cardinality and the full spectral
classification are not asserted by these conditional spectral corollaries.
No undirected-graph extension, independent human review, release or priority
claim is made here. The preceding isomorphism dichotomy is imported unchanged.
-/

set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace Couret.CayleySpectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

















end Couret.CayleySpectral
namespace Couret.CayleySpectral
/-! An exact odd-power identity, valid in every unital associative ring. -/






















end Couret.CayleySpectral

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





















end Couret.CayleyDoublet

namespace Couret.CayleyDoublet
open Couret.CayleySpectral
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]








































end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianCayleyMatrix_sq_eq_of_quotient_order_three
    (a d h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) :
    abelianCayleyMatrix (AbelianSource a d h) ^ 2 =
      abelianCayleyMatrix (AbelianTarget a d h) ^ 2 := by sorry
























end Couret.CayleyDoublet
