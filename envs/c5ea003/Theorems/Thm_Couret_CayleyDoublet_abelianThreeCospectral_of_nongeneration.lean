-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThreeCospectral_of_nongeneration
-- name    : Couret.CayleyDoublet.abelianThreeCospectral_of_nongeneration
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:29:55.824195+00:00
-- url     : https://prove2.me/theorems/570da742-a2c1-4589-b5b8-16092c27ebad
-- title:
--   Cospectrality from nongeneration
-- statement:
--   Let $G$ be a finite abelian group. Suppose $a,d,h\in G$, $2h=0$, $h\ne0$, and the image of $d$ in $G/\langle h\rangle$ has exact order three. Write $S=\{a,a+d,a+d+h\}$ and $T=\{a,a-d,a-d+h\}$, and let $A_U(x,y)=1$ if $y-x\in U$ and $0$ otherwise, with rational entries. Assume additionally $\langle a,d,h\rangle=G$ and $\langle a,h\rangle\ne G$. Then
--
--   $$\operatorname{charpoly}(A_S)=\operatorname{charpoly}(A_T).$$
--
--   This establishes the nongeneration branch of directed cospectrality.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L585-L597, lines 585–597; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleyDoublet.abelianThreeCospectral_of_nongeneration

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThreeIso_iff_nongeneration_of_quotient_order_three
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

theorem abelianThreeCospectral_of_nongeneration
    (a d h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hgen : AddSubgroup.closure ({a, d, h} : Set G) = ⊤)
    (hproper : AddSubgroup.closure ({a, h} : Set G) ≠ ⊤) :
    (abelianCayleyMatrix (AbelianSource a d h)).charpoly =
      (abelianCayleyMatrix (AbelianTarget a d h)).charpoly := by sorry














end Couret.CayleyDoublet
