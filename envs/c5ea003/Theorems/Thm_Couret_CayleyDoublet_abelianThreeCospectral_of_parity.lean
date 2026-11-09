-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThreeCospectral_of_parity
-- name    : Couret.CayleyDoublet.abelianThreeCospectral_of_parity
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:07:23.35492+00:00
-- url     : https://prove2.me/theorems/e5125e62-859d-4181-ad4d-5f7f02f1fb14
-- title:
--   Parity gives cospectral Cayley triples
-- statement:
--   Let $G$ be an abelian group. Assume $G$ finite, $a,d,h\in G$, $2h=0\ne h$, and $\bar d$ has order three in $G/\langle h\rangle$. If an additive map $\varepsilon:G\to\mathbb Z/2$ satisfies $\varepsilon(a)=1$ and $\varepsilon(h)=0$, then $$\operatorname{charpoly}(A_{S(a,d,h)})=\operatorname{charpoly}(A_{T(a,d,h)}).$$
--
--   The parity map is supplied as a hypothesis. Here $S(a,d,h)=\{a,a+d,a+d+h\}$ and $T(a,d,h)=\{a,a-d,a-d+h\}$; $A_U$ denotes the rational directed Cayley adjacency matrix of $U$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L555-L572, lines 555–572; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleyDoublet.abelianThreeCospectral_of_parity

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_parity_sign
import Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_sq_eq_of_quotient_order_three
import Theorems.Thm_Couret_CayleyDoublet_abelian_quotient_addOrderOf_three_iff
import Theorems.Thm_Couret_CayleySpectral_charpoly_eq_of_sq_eq_of_neg
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

theorem abelianThreeCospectral_of_parity
    (a d h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (ε : G →+ ZMod 2) (ha : ε a = 1) (hh : ε h = 0) :
    (abelianCayleyMatrix (AbelianSource a d h)).charpoly =
      (abelianCayleyMatrix (AbelianTarget a d h)).charpoly := by sorry


















end Couret.CayleyDoublet
