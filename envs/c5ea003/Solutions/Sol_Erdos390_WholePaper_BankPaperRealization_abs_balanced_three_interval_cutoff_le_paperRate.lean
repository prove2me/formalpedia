-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.abs_balanced_three_interval_cutoff_le_paperRate
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:34:24.038912+00:00
-- url     : https://prove2.me/submissions/f0358410-e626-46ca-9124-267699b4cbe8

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



































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCanonicalRowPaperScale -/
section


/-!
# Canonical sharp Saias row-scale geometry

This file specializes the closed sharp endpoint and fixed-head estimates to
the paper's literal balanced raw point.  The high-block multiplicity is
written as `K0 + 1`, so its positivity is built into the data rather than
assumed separately.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Uniform control of the literal balanced coefficient -/



/-- A lower bound for the integral tail gives a constant bound for the
balanced high-block coefficient. -/
theorem roughHeadBalancedAlpha_abs_le_of_tail_lower
    {W n h K : ℕ} {beta L c : ℝ}
    (hc : 0 < c) (hn : 0 < n) (hK : 0 < K) (hL : 0 < L)
    (htail : c * (n : ℝ) / L ≤ (h : ℝ)) :
    |roughHeadBalancedAlpha W n h K beta L| ≤
      1 / ((K : ℝ) * roughHeadDensity W) +
        |beta| / ((K : ℝ) * c) := by
  have hdelta : 0 < roughHeadDensity W := roughHeadDensity_pos W
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hKReal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have htailPos : 0 < c * (n : ℝ) / L := by positivity
  have hhReal : (0 : ℝ) < (h : ℝ) := htailPos.trans_le htail
  have hden :
      0 < (K : ℝ) * (h : ℝ) := mul_pos hKReal hhReal
  have hsubCast :
      (((n - K * h : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n (K * h)
  have hsubCastNonneg :
      (0 : ℝ) ≤ (((n - K * h : ℕ) : ℝ)) := by
    positivity
  have hnum :
      |(h : ℝ) / roughHeadDensity W -
          (beta / L) * (((n - K * h : ℕ) : ℝ))| ≤
        (h : ℝ) / roughHeadDensity W +
          |beta| / L * (n : ℝ) := by
    calc
      |(h : ℝ) / roughHeadDensity W -
          (beta / L) * (((n - K * h : ℕ) : ℝ))| ≤
        |(h : ℝ) / roughHeadDensity W| +
          |(beta / L) * (((n - K * h : ℕ) : ℝ))| :=
        abs_sub _ _
      _ = (h : ℝ) / roughHeadDensity W +
          (|beta| / L) * (((n - K * h : ℕ) : ℝ)) := by
        rw [abs_div, abs_of_pos hdelta, abs_of_nonneg hhReal.le,
          abs_mul, abs_div, abs_of_pos hL,
          abs_of_nonneg hsubCastNonneg]
      _ ≤ (h : ℝ) / roughHeadDensity W +
          |beta| / L * (n : ℝ) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hsubCast
            (div_nonneg (abs_nonneg beta) hL.le))
  have hcross : c * (n : ℝ) ≤ (h : ℝ) * L := by
    have := (div_le_iff₀ hL).mp htail
    simpa only [mul_comm] using this
  have hnDiv : (n : ℝ) ≤ ((h : ℝ) * L) / c :=
    (le_div_iff₀ hc).2 (by
      calc
        (n : ℝ) * c = c * (n : ℝ) := by ring
        _ ≤ (h : ℝ) * L := hcross)
  have hratio :
      (n : ℝ) / ((h : ℝ) * L) ≤ 1 / c := by
    calc
      (n : ℝ) / ((h : ℝ) * L) ≤
          (((h : ℝ) * L) / c) / ((h : ℝ) * L) :=
        div_le_div_of_nonneg_right hnDiv
          (mul_nonneg hhReal.le hL.le)
      _ = 1 / c := by field_simp
  unfold roughHeadBalancedAlpha
  norm_num only [Nat.cast_mul]
  rw [abs_div, abs_of_pos hden]
  calc
    |(h : ℝ) / roughHeadDensity W -
        (beta / L) * (((n - K * h : ℕ) : ℝ))| /
          ((K : ℝ) * (h : ℝ)) ≤
      ((h : ℝ) / roughHeadDensity W +
        |beta| / L * (n : ℝ)) /
          ((K : ℝ) * (h : ℝ)) :=
        (div_le_div_iff_of_pos_right hden).2 hnum
    _ = 1 / ((K : ℝ) * roughHeadDensity W) +
        (|beta| / (K : ℝ)) *
          ((n : ℝ) / ((h : ℝ) * L)) := by
      field_simp [hdelta.ne', hKReal.ne', hhReal.ne', hL.ne']
    _ ≤ 1 / ((K : ℝ) * roughHeadDensity W) +
        (|beta| / (K : ℝ)) * (1 / c) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hratio
          (div_nonneg (abs_nonneg beta) hKReal.le))
    _ = 1 / ((K : ℝ) * roughHeadDensity W) +
        |beta| / ((K : ℝ) * c) := by
      field_simp [hKReal.ne', hc.ne']

/-- With the paper tail and the positive multiplicity `K0+1`, the
balanced coefficient is uniformly bounded by a constant chosen before
`n`. -/
theorem roughHeadBalancedAlpha_succ_abs_le
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n : ℕ} (hn : 2 ≤ n) :
    |roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
        beta (L n)| ≤
      1 / (((K0 + 1 : ℕ) : ℝ) * roughHeadDensity W) +
        |beta| / (((K0 + 1 : ℕ) : ℝ) * c) := by
  have hL : 0 < L n := L_pos (by omega)
  have htail :
      c * (n : ℝ) / L n ≤ (upperTailLength c n : ℝ) := by
    rw [upperTailLength]
    calc
      c * (n : ℝ) / L n = c * secondOrderScale n := by
        unfold secondOrderScale L
        ring
      _ ≤ (Nat.ceil (c * secondOrderScale n) : ℝ) :=
        Nat.le_ceil (c * secondOrderScale n)
  exact roughHeadBalancedAlpha_abs_le_of_tail_lower
    hc (by omega) (by omega) hL htail

/-! ## Fixed constants for the three row ledgers -/















/-! ## Quotient and logarithmic geometry -/





























/-! ## The balanced Dickman main ledger -/





/-! ## The weighted sharp Saias transition ledger -/



/-! ## Absorption of the sharp fixed-head divisor sum -/



/-! ## One unified canonical raw-row allowance -/













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







/-! ## Positive cutoff-band algebra -/

/-- Pure positive three-interval cutoff adapter.

This theorem makes no claim that the clipped physical intervals satisfy the
three displayed size bounds.  Once those bounds are supplied, it gives the
paper's `Z/L^2+1` cutoff rate.  The broad interval is allowed the weaker
`Z/L+1` estimate because its literal coefficient is `beta/L`. -/
theorem abs_balanced_three_interval_cutoff_le_paperRate
    {W K0 n b : Nat} {c beta : Real}
    {Nplus Nhigh Nbroad Cplus Chigh Cbroad Z : Real}
    (hc : 0 < c) (hn : 2 <= n)
    (hLone : 1 <= L n) (hZ : 0 <= Z)
    (hNplus : 0 <= Nplus) (hNhigh : 0 <= Nhigh)
    (hNbroad : 0 <= Nbroad)
    (hplus : Nplus <= Cplus * (Z / L n ^ 2 + 1))
    (hhigh : Nhigh <= Chigh * (Z / L n ^ 2 + 1))
    (hbroad : Nbroad <= Cbroad * (Z / L n + 1))
    (_hCplus : 0 <= Cplus) (hChigh : 0 <= Chigh)
    (hCbroad : 0 <= Cbroad) :
    |Nplus -
        (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              beta (L n) * Nhigh +
            (beta / L n) * Nbroad)| <=
      (Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        |beta| * Cbroad) *
          (Z / L n ^ 2 + 1) := by
  let g : Real :=
    if Nat.Coprime b (roughHeadModulus W) then 1 else 0
  let alpha :=
    roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
      beta (L n)
  let q := beta / L n
  have hg : |g| <= 1 := by
    dsimp only [g]
    by_cases hcop : Nat.Coprime b (roughHeadModulus W)
    · rw [if_pos hcop]
      exact (abs_one : |(1 : Real)| = 1).le
    · simp only [if_neg hcop, abs_zero, zero_le_one]
  have halpha :
      |alpha| <= roughBalancedAlphaConstant W K0 c beta := by
    simpa only [alpha, roughBalancedAlphaConstant] using
      roughHeadBalancedAlpha_succ_abs_le W K0 hc hn
  have hL : 0 < L n := L_pos (by omega)
  have hshort0 : 0 <= Z / L n ^ 2 + 1 := by positivity
  have hbroadScale :
      (1 / L n) * (Z / L n + 1) <= Z / L n ^ 2 + 1 := by
    have hinv : 1 / L n <= 1 := (div_le_one hL).2 hLone
    calc
      (1 / L n) * (Z / L n + 1) =
          Z / L n ^ 2 + 1 / L n := by ring
      _ <= Z / L n ^ 2 + 1 := add_le_add_right hinv _
  have hraw :
      |Nplus - g * (alpha * Nhigh + q * Nbroad)| <=
        Nplus + |alpha| * Nhigh + |q| * Nbroad := by
    calc
      |Nplus - g * (alpha * Nhigh + q * Nbroad)| <=
          |Nplus| + |g * (alpha * Nhigh + q * Nbroad)| :=
        abs_sub _ _
      _ = Nplus + |g| * |alpha * Nhigh + q * Nbroad| := by
        rw [abs_of_nonneg hNplus, abs_mul]
      _ <= Nplus + 1 * |alpha * Nhigh + q * Nbroad| :=
        add_le_add_right
          (mul_le_mul_of_nonneg_right hg (abs_nonneg _)) Nplus
      _ <= Nplus + (|alpha| * Nhigh + |q| * Nbroad) := by
        rw [one_mul]
        exact add_le_add_right
          ((abs_add_le _ _).trans_eq (by
            rw [abs_mul, abs_mul, abs_of_nonneg hNhigh,
              abs_of_nonneg hNbroad])) Nplus
      _ = Nplus + |alpha| * Nhigh + |q| * Nbroad := by
        rw [add_assoc]
  change
    |Nplus - g * (alpha * Nhigh + q * Nbroad)| <= _
  calc
    |Nplus - g * (alpha * Nhigh + q * Nbroad)| <=
        Nplus + |alpha| * Nhigh + |q| * Nbroad := hraw
    _ <=
        Cplus * (Z / L n ^ 2 + 1) +
          roughBalancedAlphaConstant W K0 c beta *
            (Chigh * (Z / L n ^ 2 + 1)) +
          |beta| * Cbroad * (Z / L n ^ 2 + 1) := by
      have hhighTerm :
          |alpha| * Nhigh <=
            roughBalancedAlphaConstant W K0 c beta *
              (Chigh * (Z / L n ^ 2 + 1)) := by
        calc
          |alpha| * Nhigh <= |alpha| *
              (Chigh * (Z / L n ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_left hhigh (abs_nonneg alpha)
          _ <= roughBalancedAlphaConstant W K0 c beta *
              (Chigh * (Z / L n ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_right halpha
              (mul_nonneg hChigh hshort0)
      have hbroadTerm :
          |q| * Nbroad <=
            |beta| * Cbroad * (Z / L n ^ 2 + 1) := by
        calc
          |q| * Nbroad <= |q| * (Cbroad * (Z / L n + 1)) :=
            mul_le_mul_of_nonneg_left hbroad (abs_nonneg q)
          _ = (|beta| * Cbroad) *
              ((1 / L n) * (Z / L n + 1)) := by
            dsimp only [q]
            rw [abs_div, abs_of_pos hL]
            ring
          _ <= (|beta| * Cbroad) * (Z / L n ^ 2 + 1) :=
            mul_le_mul_of_nonneg_left hbroadScale
              (mul_nonneg (abs_nonneg beta) hCbroad)
      exact add_le_add (add_le_add hplus hhighTerm) hbroadTerm
    _ =
      (Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        |beta| * Cbroad) *
          (Z / L n ^ 2 + 1) := by ring

end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {W K0 n b : Nat} {c beta Nplus Nhigh Nbroad Cplus Chigh Cbroad Z : Real},
  LT.lt.{0} (0 : Real) c →
    LE.le.{0} (2 : Nat) n →
      LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
        LE.le.{0} (0 : Real) Z →
          LE.le.{0} (0 : Real) Nplus →
            LE.le.{0} (0 : Real) Nhigh →
              LE.le.{0} (0 : Real) Nbroad →
                LE.le.{0} Nplus
                    (HMul.hMul.{0, 0, 0} Cplus
                      (HAdd.hAdd.{0, 0, 0}
                        (HDiv.hDiv.{0, 0, 0} Z (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))) (1 : Real))) →
                  LE.le.{0} Nhigh
                      (HMul.hMul.{0, 0, 0} Chigh
                        (HAdd.hAdd.{0, 0, 0}
                          (HDiv.hDiv.{0, 0, 0} Z (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat)))
                          (1 : Real))) →
                    LE.le.{0} Nbroad
                        (HMul.hMul.{0, 0, 0} Cbroad
                          (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} Z (Erdos390.Full.Scale.L n)) (1 : Real))) →
                      LE.le.{0} (0 : Real) Cplus →
                        LE.le.{0} (0 : Real) Chigh →
                          LE.le.{0} (0 : Real) Cbroad →
                            LE.le.{0}
                              (abs.{0}
                                (HSub.hSub.{0, 0, 0} Nplus
                                  (HMul.hMul.{0, 0, 0}
                                    (ite.{1} (Nat.Coprime b (Erdos390.WholePaper.roughHeadModulus W)) (1 : Real)
                                      (0 : Real))
                                    (HAdd.hAdd.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0}
                                        (Erdos390.WholePaper.roughHeadBalancedAlpha W n
                                          (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                          beta (Erdos390.Full.Scale.L n))
                                        Nhigh)
                                      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} beta (Erdos390.Full.Scale.L n))
                                        Nbroad)))))
                              (HMul.hMul.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0}
                                  (HAdd.hAdd.{0, 0, 0} Cplus
                                    (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughBalancedAlphaConstant W K0 c beta)
                                      Chigh))
                                  (HMul.hMul.{0, 0, 0} (abs.{0} beta) Cbroad))
                                (HAdd.hAdd.{0, 0, 0}
                                  (HDiv.hDiv.{0, 0, 0} Z (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat)))
                                  (1 : Real))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.abs_balanced_three_interval_cutoff_le_paperRate
