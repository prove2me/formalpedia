-- Prove2me | Theorems.Thm_Couret_CayleySpectral_charpoly_eq_of_sq_eq_of_neg
-- name    : Couret.CayleySpectral.charpoly_eq_of_sq_eq_of_neg
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:22.450443+00:00
-- url     : https://prove2.me/theorems/61d7070c-e492-4339-af91-36dd2cbc73f1
-- title:
--   Equal squares and sign symmetry force equal characteristic polynomials
-- statement:
--   Let $R$ be a commutative ring with no zero divisors and let $A,B$ be square matrices indexed by the same finite type. If $A^2=B^2$ and each matrix has the same characteristic polynomial as its negative, then
--
--   $$\chi_A(X)=\chi_B(X).$$
--
--   The indexing type may be empty; no restriction on characteristic is imposed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyTwoColourSpectral.lean#L33-L62, lines 33–62; source file SHA-256 c35f0bcb235d6cfd9ce9cf16e4ece0a784c0c18ed967e268865d8a9c061aa16b; theorem Couret.CayleySpectral.charpoly_eq_of_sq_eq_of_neg

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

theorem charpoly_eq_of_sq_eq_of_neg [NoZeroDivisors R] (A B : Matrix ι ι R)
    (hsq : A ^ 2 = B ^ 2)
    (hA : (-A).charpoly = A.charpoly)
    (hB : (-B).charpoly = B.charpoly) :
    A.charpoly = B.charpoly := by sorry














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
