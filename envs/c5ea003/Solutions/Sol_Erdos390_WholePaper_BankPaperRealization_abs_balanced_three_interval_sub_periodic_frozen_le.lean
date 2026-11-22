-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.abs_balanced_three_interval_sub_periodic_frozen_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:13:13.314485+00:00
-- url     : https://prove2.me/submissions/483a01e7-63b9-41cd-ba6b-cc3879e63ada

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)











theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.WholePaper.RoughHeadCompatibleFinitePoint -/
section


/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/





















/-! ## The finite head and raw weights -/









/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero



/-- The complete zero-head stratum has strictly positive density. -/
theorem roughHeadDensity_pos (W : ℕ) :
    0 < roughHeadDensity W := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot : (0 : ℝ) < ((roughHeadModulus W).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (roughHeadModulus_pos W)
  exact div_pos htot hmod



/-- The defining quotient for `roughHeadBalancedAlpha` gives the exact
real-length balance as soon as the high block has positive length. -/
theorem roughHeadBalancedAlpha_length_normalization
    {W n h K : ℕ} {beta L : ℝ} (hKhPos : 0 < K * h) :
    roughHeadDensity W *
        (roughHeadBalancedAlpha W n h K beta L *
            (((K * h : ℕ) : ℝ)) +
          (beta / L) * (((n - K * h : ℕ) : ℝ))) =
      ((h : ℕ) : ℝ) := by
  have hdelta : roughHeadDensity W ≠ 0 :=
    (roughHeadDensity_pos W).ne'
  have hKhReal : (((K * h : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hKhPos.ne'
  rw [roughHeadBalancedAlpha, div_mul_cancel₀ _ hKhReal,
    sub_add_cancel]
  calc
    roughHeadDensity W * (((h : ℕ) : ℝ) / roughHeadDensity W) =
        ((((h : ℕ) : ℝ) * roughHeadDensity W) /
          roughHeadDensity W) := by ring
    _ = ((h : ℕ) : ℝ) := mul_div_cancel_right₀ _ hdelta































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveSignedCoreErrorAdapter -/
section


/-!
# Error adapter from the four/five assembly to a signed smooth core

The four/five continuum calculation ends with a completely explicit error
ledger.  This file performs the remaining algebra needed by the signed
exceptional-core argument:

* compress the four factorially weighted assembly errors to one
  `Z / log(y)^3` bound;
* add the repeated-prime transfer and convert `log(y)` to the paper scale
  `L`;
* freeze the continuum mixture kernel at one reference logarithmic
  coordinate;
* expose the exact balanced normalization for the paper multiplicity
  `K0 + 1`;
* combine three independently estimated physical intervals without losing
  the signed periodic main term.

The module deliberately does not identify a literal smooth-core fibre with
the three rough intervals.  That finite reindexing is an independent input
to the final connector.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Compression of the explicit four-layer error ledger -/

















/-! ## Freezing the common continuum kernel -/







/-! ### Quotient endpoints and ideal physical lengths -/





/-! ## Exact `K0+1` balance and signed three-interval algebra -/

/-- Exact physical-length normalization after division by one positive
smooth core.  The indicator is the literal head-free indicator, so the
right side is exactly the mean-zero periodic core coefficient. -/
theorem roughHeadBalancedAlpha_succ_div_core_normalization
    {W K0 n h b : Nat} {beta ell : Real}
    (hKh : 0 < (K0 + 1) * h) :
    (h : Real) / (b : Real) -
        (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
          (roughHeadBalancedAlpha W n h (K0 + 1) beta ell *
              (((K0 + 1) * h : Nat) : Real) / (b : Real) +
            (beta / ell) *
              (((n - (K0 + 1) * h : Nat) : Real)) / (b : Real)) =
      ((h : Real) / (b : Real)) *
        roughHeadPeriodicCoreCoefficient W b := by
  have hdelta : roughHeadDensity W ≠ 0 :=
    (roughHeadDensity_pos W).ne'
  have hnormalization :=
    roughHeadBalancedAlpha_length_normalization
      (W := W) (n := n) (h := h) (K := K0 + 1)
      (beta := beta) (L := ell) hKh
  have hinside :
      roughHeadBalancedAlpha W n h (K0 + 1) beta ell *
            (((K0 + 1) * h : Nat) : Real) +
          (beta / ell) *
            (((n - (K0 + 1) * h : Nat) : Real)) =
        (h : Real) / roughHeadDensity W := by
    apply (eq_div_iff hdelta).2
    simpa only [mul_comm] using hnormalization
  have hinsideDiv :
      roughHeadBalancedAlpha W n h (K0 + 1) beta ell *
            (((K0 + 1) * h : Nat) : Real) / (b : Real) +
          (beta / ell) *
            (((n - (K0 + 1) * h : Nat) : Real)) / (b : Real) =
        ((h : Real) / roughHeadDensity W) / (b : Real) := by
    rw [← add_div, hinside]
  by_cases hcop : Nat.Coprime b (roughHeadModulus W)
  · rw [if_pos hcop]
    unfold roughHeadPeriodicCoreCoefficient
    rw [if_pos hcop, hinsideDiv]
    ring
  · rw [if_neg hcop]
    unfold roughHeadPeriodicCoreCoefficient
    rw [if_neg hcop]
    ring

/-- Three independently frozen physical intervals retain the exact signed
periodic main term after balanced normalization.

This is the clean input boundary expected from the finite smooth-core
reindexing: `Nplus`, `Nhigh`, and `Nbroad` are the three real interval
counts after that reindexing. -/
theorem abs_balanced_three_interval_sub_periodic_frozen_le
    {W K0 n h b : Nat} {beta ell logY kernelValue : Real}
    {Nplus Nhigh Nbroad Eplus Ehigh Ebroad : Real}
    (hKh : 0 < (K0 + 1) * h)
    (hplus :
      |Nplus -
        (kernelValue / logY) * ((h : Real) / (b : Real))| <= Eplus)
    (hhigh :
      |Nhigh -
        (kernelValue / logY) *
          ((((K0 + 1) * h : Nat) : Real) / (b : Real))| <= Ehigh)
    (hbroad :
      |Nbroad -
        (kernelValue / logY) *
          ((((n - (K0 + 1) * h : Nat) : Real)) / (b : Real))| <=
            Ebroad) :
    |Nplus -
        (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
          (roughHeadBalancedAlpha W n h (K0 + 1) beta ell * Nhigh +
            (beta / ell) * Nbroad) -
        ((kernelValue / logY) * ((h : Real) / (b : Real)) *
          roughHeadPeriodicCoreCoefficient W b)| <=
      Eplus +
        |roughHeadBalancedAlpha W n h (K0 + 1) beta ell| * Ehigh +
        |beta / ell| * Ebroad := by
  let g : Real :=
    if Nat.Coprime b (roughHeadModulus W) then 1 else 0
  let alpha := roughHeadBalancedAlpha W n h (K0 + 1) beta ell
  let q := beta / ell
  let k := kernelValue / logY
  let lplus := (h : Real) / (b : Real)
  let lhigh := (((K0 + 1) * h : Nat) : Real) / (b : Real)
  let lbroad := (((n - (K0 + 1) * h : Nat) : Real)) / (b : Real)
  have hnormalize :
      lplus - g * (alpha * lhigh + q * lbroad) =
        lplus * roughHeadPeriodicCoreCoefficient W b := by
    dsimp only [g, alpha, q, lplus, lhigh, lbroad]
    calc
      (h : Real) / (b : Real) -
          (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
            (roughHeadBalancedAlpha W n h (K0 + 1) beta ell *
                ((((K0 + 1) * h : Nat) : Real) / (b : Real)) +
              (beta / ell) *
                ((((n - (K0 + 1) * h : Nat) : Real)) / (b : Real))) =
        (h : Real) / (b : Real) -
          (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
            (roughHeadBalancedAlpha W n h (K0 + 1) beta ell *
                  (((K0 + 1) * h : Nat) : Real) / (b : Real) +
              (beta / ell) *
                  (((n - (K0 + 1) * h : Nat) : Real)) / (b : Real)) := by
        ring
      _ = ((h : Real) / (b : Real)) *
          roughHeadPeriodicCoreCoefficient W b :=
        roughHeadBalancedAlpha_succ_div_core_normalization
          (W := W) (K0 := K0) (n := n) (h := h) (b := b)
          (beta := beta) (ell := ell) hKh
  have hg : |g| <= 1 := by
    dsimp only [g]
    by_cases hcop : Nat.Coprime b (roughHeadModulus W)
    · calc
        |if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0| =
            1 := by rw [if_pos hcop, abs_one]
        _ <= 1 := le_rfl
    · calc
        |if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0| =
            0 := by rw [if_neg hcop, abs_zero]
        _ <= 1 := zero_le_one
  have hrewrite :
      Nplus - g * (alpha * Nhigh + q * Nbroad) -
          (k * lplus * roughHeadPeriodicCoreCoefficient W b) =
        (Nplus - k * lplus) -
          g * (alpha * (Nhigh - k * lhigh) +
            q * (Nbroad - k * lbroad)) := by
    calc
      Nplus - g * (alpha * Nhigh + q * Nbroad) -
          (k * lplus * roughHeadPeriodicCoreCoefficient W b) =
        Nplus - g * (alpha * Nhigh + q * Nbroad) -
          k * (lplus * roughHeadPeriodicCoreCoefficient W b) := by ring
      _ =
        Nplus - g * (alpha * Nhigh + q * Nbroad) -
          k * (lplus - g * (alpha * lhigh + q * lbroad)) := by
        rw [hnormalize]
      _ =
        (Nplus - k * lplus) -
          g * (alpha * (Nhigh - k * lhigh) +
            q * (Nbroad - k * lbroad)) := by ring
  change
    |Nplus - g * (alpha * Nhigh + q * Nbroad) -
        (k * lplus * roughHeadPeriodicCoreCoefficient W b)| <= _
  rw [hrewrite]
  have hinner :
      |alpha * (Nhigh - k * lhigh) +
          q * (Nbroad - k * lbroad)| <=
        |alpha| * Ehigh + |q| * Ebroad := by
    calc
      |alpha * (Nhigh - k * lhigh) +
          q * (Nbroad - k * lbroad)| <=
        |alpha * (Nhigh - k * lhigh)| +
          |q * (Nbroad - k * lbroad)| := abs_add_le _ _
      _ =
        |alpha| * |Nhigh - k * lhigh| +
          |q| * |Nbroad - k * lbroad| := by
        rw [abs_mul, abs_mul]
      _ <= |alpha| * Ehigh + |q| * Ebroad :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (by simpa only [alpha, k, lhigh] using hhigh)
            (abs_nonneg alpha))
          (mul_le_mul_of_nonneg_left
            (by simpa only [q, k, lbroad] using hbroad)
            (abs_nonneg q))
  have hinnerRhs0 :
      0 <= |alpha| * Ehigh + |q| * Ebroad := by
    have hEhigh0 : 0 <= Ehigh :=
      (abs_nonneg (Nhigh - k * lhigh)).trans
        (by simpa only [alpha, k, lhigh] using hhigh)
    have hEbroad0 : 0 <= Ebroad :=
      (abs_nonneg (Nbroad - k * lbroad)).trans
        (by simpa only [q, k, lbroad] using hbroad)
    positivity
  calc
    |(Nplus - k * lplus) -
        g * (alpha * (Nhigh - k * lhigh) +
          q * (Nbroad - k * lbroad))| <=
      |Nplus - k * lplus| +
        |g * (alpha * (Nhigh - k * lhigh) +
          q * (Nbroad - k * lbroad))| := abs_sub _ _
    _ =
      |Nplus - k * lplus| +
        |g| * |alpha * (Nhigh - k * lhigh) +
          q * (Nbroad - k * lbroad)| := by rw [abs_mul]
    _ <=
      Eplus + |g| * (|alpha| * Ehigh + |q| * Ebroad) :=
      add_le_add
        (by simpa only [k, lplus] using hplus)
        (mul_le_mul_of_nonneg_left hinner (abs_nonneg g))
    _ <= Eplus + 1 * (|alpha| * Ehigh + |q| * Ebroad) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_right hg hinnerRhs0) Eplus
    _ =
      Eplus + |alpha| * Ehigh + |q| * Ebroad := by ring



/-! ## Positive cutoff-band algebra -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {W K0 n h b : Nat} {beta ell logY kernelValue Nplus Nhigh Nbroad Eplus Ehigh Ebroad : Real},
  LT.lt.{0} (0 : Nat) (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) h) →
    LE.le.{0}
        (abs.{0}
          (HSub.hSub.{0, 0, 0} Nplus
            (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} kernelValue logY) (HDiv.hDiv.{0, 0, 0} ↑h ↑b))))
        Eplus →
      LE.le.{0}
          (abs.{0}
            (HSub.hSub.{0, 0, 0} Nhigh
              (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} kernelValue logY)
                (HDiv.hDiv.{0, 0, 0} ↑(HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) h) ↑b))))
          Ehigh →
        LE.le.{0}
            (abs.{0}
              (HSub.hSub.{0, 0, 0} Nbroad
                (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} kernelValue logY)
                  (HDiv.hDiv.{0, 0, 0}
                    ↑(HSub.hSub.{0, 0, 0} n (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) h)) ↑b))))
            Ebroad →
          LE.le.{0}
            (abs.{0}
              (HSub.hSub.{0, 0, 0}
                (HSub.hSub.{0, 0, 0} Nplus
                  (HMul.hMul.{0, 0, 0}
                    (ite.{1} (Nat.Coprime b (Erdos390.WholePaper.roughHeadModulus W)) (1 : Real) (0 : Real))
                    (HAdd.hAdd.{0, 0, 0}
                      (HMul.hMul.{0, 0, 0}
                        (Erdos390.WholePaper.roughHeadBalancedAlpha W n h (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) beta ell)
                        Nhigh)
                      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} beta ell) Nbroad))))
                (HMul.hMul.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} kernelValue logY) (HDiv.hDiv.{0, 0, 0} ↑h ↑b))
                  (Erdos390.WholePaper.BankPaperRealization.roughHeadPeriodicCoreCoefficient W b))))
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0} Eplus
                (HMul.hMul.{0, 0, 0}
                  (abs.{0}
                    (Erdos390.WholePaper.roughHeadBalancedAlpha W n h (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) beta ell))
                  Ehigh))
              (HMul.hMul.{0, 0, 0} (abs.{0} (HDiv.hDiv.{0, 0, 0} beta ell)) Ebroad)) := by
  exact @Erdos390.WholePaper.BankPaperRealization.abs_balanced_three_interval_sub_periodic_frozen_le
