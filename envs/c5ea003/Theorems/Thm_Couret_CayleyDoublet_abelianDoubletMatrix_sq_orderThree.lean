-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianDoubletMatrix_sq_orderThree
-- name    : Couret.CayleyDoublet.abelianDoubletMatrix_sq_orderThree
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:45:23.782887+00:00
-- url     : https://prove2.me/theorems/6438ceed-0b0b-4e5b-ab0b-6cd45329ea1b
-- title:
--   Doublet matrix square under the third-order relation
-- statement:
--   Let $G$ be a finite abelian group. For $d,h\in G$, let $P_t(x,y)=1$ if $y=x+t$ and zero otherwise, and $D(d,h)=P_d+P_{d+h}$. If $2h=0$ and $3d\in\{0,h\}$, then
--
--   $$D(d,h)^2=2D(-d,h).$$
--
--   This algebraic matrix identity allows $h=0$ and repeated translations.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L318-L339, lines 318–339; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleyDoublet.abelianDoubletMatrix_sq_orderThree

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
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

theorem abelianDoubletMatrix_sq_orderThree (d h : G)
    (hhalf : h + h = 0)
    (hthree : (d + d) + d = 0 ∨ (d + d) + d = h) :
    abelianDoubletMatrix d h ^ 2 = 2 * abelianDoubletMatrix (-d) h := by sorry




































end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



























end Couret.CayleyDoublet
