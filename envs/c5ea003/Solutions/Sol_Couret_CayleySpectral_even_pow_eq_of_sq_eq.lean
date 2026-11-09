-- Prove2me | solution 1 for Couret.CayleySpectral.even_pow_eq_of_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:28.032703+00:00
-- url     : https://prove2.me/submissions/49b7de11-4200-46ba-91a5-58cc76ed30bc

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











theorem p2m_local_even_pow_eq_of_sq_eq
    {M : Type*} [Monoid M] (x y : M)
    (hsq : x ^ 2 = y ^ 2) (n : ℕ) : x ^ (2 * n) = y ^ (2 * n) := by
  rw [pow_mul, pow_mul, hsq]










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


universe p2m_u_0
theorem solution : ∀ {M : Type p2m_u_0} [inst : Monoid.{p2m_u_0} M] (x y : M),
  @Eq.{p2m_u_0 + 1} M
      (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} M Nat M (@instHPow.{p2m_u_0, 0} M Nat (@Monoid.toPow.{p2m_u_0} M inst)) x
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} M Nat M (@instHPow.{p2m_u_0, 0} M Nat (@Monoid.toPow.{p2m_u_0} M inst)) y
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
    ∀ (n : Nat),
      @Eq.{p2m_u_0 + 1} M
        (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} M Nat M (@instHPow.{p2m_u_0, 0} M Nat (@Monoid.toPow.{p2m_u_0} M inst)) x
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
        (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} M Nat M (@instHPow.{p2m_u_0, 0} M Nat (@Monoid.toPow.{p2m_u_0} M inst)) y
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)) := @_root_.Couret.CayleySpectral.p2m_local_even_pow_eq_of_sq_eq

