-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_source_target_eq_translationTriple
-- name    : Couret.CayleyDoublet.abelianCayleyMatrix_source_target_eq_translationTriple
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:27.608+00:00
-- url     : https://prove2.me/theorems/b4b7b1d2-d234-4d2a-a327-6061b74629f8
-- title:
--   Cayley matrices as translation sums
-- statement:
--   Let $G$ be an abelian group. For $a,d,h\in G$, assume $G$ finite, $h\ne0$, $2h=0$, and $d$ has order three in $G/\langle h\rangle$. The rational adjacency matrices for the source and reflected target equal their translation-triple matrices: $$A_{S(a,d,h)}=\mathcal T(a,d,h),\qquad A_{T(a,d,h)}=\mathcal T(a,-d,h).$$
--
--   This identifies finite-set adjacency with translation sums under the exact quotient-order hypothesis. Here $S(a,d,h)=\{a,a+d,a+d+h\}$ and $T(a,d,h)=\{a,a-d,a-d+h\}$; $A_U$ denotes the rational directed Cayley adjacency matrix of $U$. Here $\mathcal T(a,d,h)=T_a+T_{a+d}+T_{a+d+h}$ and $T_t$ is the single-shift matrix.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L611-L629, lines 611–629; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleyDoublet.abelianCayleyMatrix_source_target_eq_translationTriple

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
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

theorem abelianCayleyMatrix_source_target_eq_translationTriple
    (a d h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) :
    abelianCayleyMatrix (AbelianSource a d h) = abelianTranslationTriple a d h ∧
      abelianCayleyMatrix (AbelianTarget a d h) = abelianTranslationTriple a (-d) h := by sorry










end Couret.CayleyDoublet
