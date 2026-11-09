-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_ne_iff
-- name    : Couret.CayleyDoublet.abelianThree_odd_trace_ne_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:15:53.201429+00:00
-- url     : https://prove2.me/theorems/1d1716f3-5994-40b6-8be7-e8e133e3b86d
-- title:
--   Exact odd-trace separation criterion
-- statement:
--   Let $G$ be an abelian group. Assume $G$ finite, $a,d,h\in G$, $2h=0\ne h$, and $\bar d$ has order three modulo $\langle h\rangle$. For each natural $m$, $$\operatorname{tr}(A_S^{2m+1})\ne\operatorname{tr}(A_T^{2m+1})\iff (2m+1)a+d\in\langle h\rangle\ \text{or}\ (2m+1)a-d\in\langle h\rangle.$$
--
--   This includes $m=0$ and characterizes exactly which odd traces differ. Here $S(a,d,h)=\{a,a+d,a+d+h\}$ and $T(a,d,h)=\{a,a-d,a-d+h\}$; $A_U$ denotes the rational directed Cayley adjacency matrix of $U$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L683-L711, lines 683–711; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleyDoublet.abelianThree_odd_trace_ne_iff

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_sub
import Theorems.Thm_Couret_CayleyDoublet_abelian_mem_zmultiples_halfTurn_iff
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

theorem abelianThree_odd_trace_ne_iff
    (a d h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) (n : ℕ) :
    Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ (2 * n + 1)) ≠
      Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ (2 * n + 1)) ↔
        (2 * n + 1) • a + d ∈ AddSubgroup.zmultiples h ∨
          (2 * n + 1) • a - d ∈ AddSubgroup.zmultiples h := by sorry


end Couret.CayleyDoublet
