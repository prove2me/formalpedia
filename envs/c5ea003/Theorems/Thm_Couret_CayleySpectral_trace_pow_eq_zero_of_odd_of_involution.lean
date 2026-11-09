-- Prove2me | Theorems.Thm_Couret_CayleySpectral_trace_pow_eq_zero_of_odd_of_involution
-- name    : Couret.CayleySpectral.trace_pow_eq_zero_of_odd_of_involution
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:21:06.571629+00:00
-- url     : https://prove2.me/theorems/ddf75041-2931-4e18-9604-18573758f314
-- title:
--   Odd traces vanish under an anticommuting involution
-- statement:
--   Let $A,D$ be square rational matrices indexed by a finite set, with $D^2=I$ and $DAD=-A$. For each odd $n\in\mathbb N$,
--
--   $$\operatorname{tr}(A^n)=0.$$
--
--   This supplies the matrix parity argument for odd closed-walk counts.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L101-L117, lines 101–117; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleySpectral.trace_pow_eq_zero_of_odd_of_involution

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

theorem trace_pow_eq_zero_of_odd_of_involution (A D : Matrix ι ι ℚ)
    (hD : D * D = 1) (hA : D * A * D = -A) (n : ℕ) (hn : Odd n) :
    Matrix.trace (A ^ n) = 0 := by sorry




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



























end Couret.CayleyDoublet
