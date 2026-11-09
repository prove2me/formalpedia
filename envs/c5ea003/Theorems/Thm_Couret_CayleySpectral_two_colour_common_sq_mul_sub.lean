-- Prove2me | Theorems.Thm_Couret_CayleySpectral_two_colour_common_sq_mul_sub
-- name    : Couret.CayleySpectral.two_colour_common_sq_mul_sub
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:21.80014+00:00
-- url     : https://prove2.me/theorems/8c7fcb3e-94d8-4436-88ef-f8101635b82f
-- title:
--   A common-square identity for two commuting colours
-- statement:
--   Let $R$ be a unital associative ring and let $u,v\in R$ commute. If $u^2=2v$ and $v^2=2u$, then
--
--   $$(1+u)^2((1+u)-(1+v))=-3((1+u)-(1+v)).$$
--
--   This identity requires neither commutativity of the whole ring nor division.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L155-L172, lines 155–172; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleySpectral.two_colour_common_sq_mul_sub

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

theorem two_colour_common_sq_mul_sub
    {R : Type*} [Ring R] (u v : R)
    (huv : Commute u v)
    (hu : u ^ 2 = 2 * v) (hv : v ^ 2 = 2 * u) :
    (1 + u) ^ 2 * ((1 + u) - (1 + v)) =
      (-3) * ((1 + u) - (1 + v)) := by sorry
















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



























end Couret.CayleyDoublet
