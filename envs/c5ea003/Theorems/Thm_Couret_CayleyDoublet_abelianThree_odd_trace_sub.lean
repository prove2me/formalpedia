-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_sub
-- name    : Couret.CayleyDoublet.abelianThree_odd_trace_sub
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:11:14.354265+00:00
-- url     : https://prove2.me/theorems/b642369b-e633-4bed-99c8-dc44287025af
-- title:
--   Odd trace difference for an order-three quotient doublet
-- statement:
--   Let G be a finite additive commutative group with decidable equality. Let a,d,h∈G satisfy h+h=0, h≠0, and let the image of d in G/⟨h⟩ have additive order exactly three, where ⟨h⟩ is the subgroup of integer multiples of h. Set S={a,a+d,a+d+h} and T={a,a−d,a−d+h}; their rational directed Cayley matrices are A_U(x,y)=1 when y−x∈U and zero otherwise, including possible loops. For every natural n, tr(A_S^(2n+1))−tr(A_T^(2n+1)) equals (−3)^n times |G|·(1[(2n+1)a+d∈⟨h⟩]−1[(2n+1)a−d∈⟨h⟩]), as a rational equality. There is no generation or cyclicity assumption, and n=0 is included.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L662-L681, lines 662–681; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleyDoublet.abelianThree_odd_trace_sub

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_source_target_eq_translationTriple
import Theorems.Thm_Couret_CayleyDoublet_abelianDoubletMatrix_sq_orderThree
import Theorems.Thm_Couret_CayleyDoublet_abelian_halfTurn_return_pair
import Theorems.Thm_Couret_CayleyDoublet_abelian_mem_zmultiples_halfTurn_iff
import Theorems.Thm_Couret_CayleyDoublet_abelian_quotient_addOrderOf_three_iff
import Theorems.Thm_Couret_CayleySpectral_two_colour_common_sq_mul_sub
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

theorem abelianThree_odd_trace_sub
    (a d h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) (n : ℕ) :
    Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ (2 * n + 1)) -
      Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ (2 * n + 1)) =
      (-3 : ℚ) ^ n *
        ((if (2 * n + 1) • a + d ∈ AddSubgroup.zmultiples h
          then (Fintype.card G : ℚ) else 0) -
         (if (2 * n + 1) • a - d ∈ AddSubgroup.zmultiples h
          then (Fintype.card G : ℚ) else 0)) := by sorry




end Couret.CayleyDoublet
