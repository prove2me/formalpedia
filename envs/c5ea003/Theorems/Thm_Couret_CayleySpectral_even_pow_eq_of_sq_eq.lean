-- Prove2me | Theorems.Thm_Couret_CayleySpectral_even_pow_eq_of_sq_eq
-- name    : Couret.CayleySpectral.even_pow_eq_of_sq_eq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:25.16259+00:00
-- url     : https://prove2.me/theorems/c0672cd2-e5ad-44b2-b511-329700d7f114
-- title:
--   Equal squares give equal even powers
-- statement:
--   Let $x,y$ belong to a monoid and satisfy $x^2=y^2$. For every natural $n$, $$x^{2n}=y^{2n}.$$
--
--   This includes zero and requires no commutativity.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L186-L189, lines 186–189; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleySpectral.even_pow_eq_of_sq_eq

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

theorem even_pow_eq_of_sq_eq
    {M : Type*} [Monoid M] (x y : M)
    (hsq : x ^ 2 = y ^ 2) (n : ℕ) : x ^ (2 * n) = y ^ (2 * n) := by sorry











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
