-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelian_halfTurn_return_pair
-- name    : Couret.CayleyDoublet.abelian_halfTurn_return_pair
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:15.013775+00:00
-- url     : https://prove2.me/theorems/c4f330d9-d9eb-4109-bf47-7a8c0f94e359
-- title:
--   A half-turn return indicator
-- statement:
--   Let $G$ be a finite abelian group. Let $z,h\in G$ and $N\in\mathbb Q$, with $2h=0$ and $h\ne0$. Then
--
--   $$N[\,z=0\,]+N[\,z+h=0\,]=N[\,z\in\{0,h\}\,].$$
--
--   This combines two mutually exclusive return conditions.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L453-L470, lines 453–470; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleyDoublet.abelian_halfTurn_return_pair

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

omit [Fintype G] in
theorem abelian_halfTurn_return_pair (z h : G) (N : ℚ)
    (hhalf : h + h = 0) (hne : h ≠ 0) :
    (if z = 0 then N else 0) + (if z + h = 0 then N else 0) =
      if z = 0 ∨ z = h then N else 0 := by sorry






end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



























end Couret.CayleyDoublet
