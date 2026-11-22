-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:28:41.103177+00:00
-- url     : https://prove2.me/submissions/83c6d47b-4675-45aa-a58a-d0801938fb40

import Definitions.Def_erdos390_remaining_analytic_propositions_007
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate_compact


section
universe u_1
theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate : Erdos390.RemainingAnalyticGoal007_005.{u_1} := @Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate_compact
end
/- Source module: Erdos390.Full.PaperScaleMarkedCell -/
section


/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/















/-! ## The common paper-scale main term -/

















/-- Four marks keep the paper coordinate inside the range on which the
constructed Dickman function is positive. -/
theorem paperDivisorCoordinate_mem_zero_five {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4) :
    0 ≤ paperDivisorCoordinate n d ∧ paperDivisorCoordinate n d ≤ 5 := by
  have hnpos : 0 < n := by omega
  have hypos : 0 < y n := y_pos hnpos
  have hylog : 0 < Real.log (y n) := by
    rw [log_y hnpos]
    exact mul_pos (by norm_num) (L_pos hn)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  have hyNatPos : 0 < yNat n := by
    by_contra hnot
    have hyNat0 : yNat n = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hyNat0] at hd4
    omega
  have hyNatRpos : (0 : ℝ) < (yNat n : ℝ) := by exact_mod_cast hyNatPos
  have hdCast : (d : ℝ) ≤ (yNat n : ℝ) ^ 4 := by exact_mod_cast hd4
  have hlogdNat : Real.log (d : ℝ) ≤
      4 * Real.log (yNat n : ℝ) := by
    have h := Real.log_le_log hdR hdCast
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hyNatUpper : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le hypos.le
  have hlogNatY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatRpos hyNatUpper
  have hlogdY : Real.log (d : ℝ) ≤ 4 * Real.log (y n) := by
    calc
      Real.log (d : ℝ) ≤ 4 * Real.log (yNat n : ℝ) := hlogdNat
      _ ≤ 4 * Real.log (y n) := by linarith
  have hquot0 : 0 ≤ Real.log (d : ℝ) / Real.log (y n) :=
    div_nonneg hlogd0 hylog.le
  have hquot4 : Real.log (d : ℝ) / Real.log (y n) ≤ 4 :=
    (div_le_iff₀ hylog).2 (by simpa using hlogdY)
  unfold paperDivisorCoordinate DickmanBasic.U
  constructor <;> linarith

theorem paperDivisibilityMain_nonneg_le {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4) :
    0 ≤ paperDivisibilityMain n d ∧
      paperDivisibilityMain n d ≤
        1 / (rho DickmanBasic.U * (d : ℝ)) := by
  have hv := paperDivisorCoordinate_mem_zero_five hn hd hd4
  have hrv : 0 < rho (paperDivisorCoordinate n d) :=
    rho_pos_on_zero_five hv.1 hv.2
  have hrv1 : rho (paperDivisorCoordinate n d) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hv.2
  have hrU : 0 < rho DickmanBasic.U := rho_U_pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold paperDivisibilityMain
  constructor
  · positivity
  · rw [div_div]
    exact div_le_div_of_nonneg_right hrv1 (mul_pos hrU hdR).le



















/-! ## Normalization algebra -/











end

end Erdos390.Full.PaperScaleMarkedCell

end

/- Source module: Erdos390.Full.LocalFugacityBounds -/
section


/-!
# Uniform bounds for restored local fugacity coefficients

The local restoration in Lemma 7.5 must retain both the factor `1 / L`
and the geometric factor `p^{-r}`.  Cardinality bounds on the exponent set
are too crude for that purpose.  This module proves the required shifted
geometric estimates directly for the actual coefficients
`exp (eta/L)^a - exp (eta/L)^(a-1)`.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacityBounds

open LocalFugacity

noncomputable section

private theorem sub_injective_on_Icc (k A : ℕ) :
    Set.InjOn (fun a : ℕ ↦ a - k) (↑(Finset.Icc k A) : Set ℕ) := by
  intro a ha b hb hab
  have hka : k ≤ a := (Finset.mem_Icc.mp ha).1
  have hkb : k ≤ b := (Finset.mem_Icc.mp hb).1
  change a - k = b - k at hab
  calc
    a = (a - k) + k := (Nat.sub_add_cancel hka).symm
    _ = (b - k) + k := congrArg (fun z : ℕ ↦ z + k) hab
    _ = b := Nat.sub_add_cancel hkb





private theorem summable_linearHalfTerm : Summable linearHalfTerm := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable
      (fun i : ℕ ↦ 3 * (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two.mul_left 3
  convert hlin.add hconst using 1
  funext i
  unfold linearHalfTerm
  ring

private theorem tsum_linearHalfTerm_eq_eight :
    ∑' i : ℕ, linearHalfTerm i = 8 := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable
      (fun i : ℕ ↦ 3 * (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two.mul_left 3
  rw [show linearHalfTerm = fun i : ℕ ↦
      (i : ℝ) * (1 / (2 : ℝ)) ^ i +
        3 * (1 / (2 : ℝ)) ^ i by
    funext i
    unfold linearHalfTerm
    ring]
  rw [hlin.tsum_add hconst,
    tsum_coe_mul_geometric_of_norm_lt_one hx,
    tsum_mul_left, tsum_geometric_two]
  norm_num

/-- Shifted arithmetic--geometric tails have an absolute numerical bound.
This is the aggregate `r+1` ledger used below. -/
theorem sum_shifted_linear_half_le_eight (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
        ((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) ≤ 8 := by
  let s := Finset.Icc 2 R
  let g : ℕ → ℕ := fun r ↦ r - 2
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc 2 R
  have heq :
      (∑ r ∈ s, ((r : ℝ) + 1) *
          (1 / (2 : ℝ)) ^ (r - 2)) =
        ∑ i ∈ s.image g, linearHalfTerm i := by
    symm
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      unfold linearHalfTerm g
      norm_num only [Nat.cast_sub hr2]
      ring
    · exact hinj
  rw [heq]
  exact (summable_linearHalfTerm.sum_le_tsum (s.image g)
      (fun i hi ↦ by unfold linearHalfTerm; positivity)).trans_eq
    tsum_linearHalfTerm_eq_eight



/-- The complete finite `r+1` reciprocal-power ledger begins at `p^{-2}`
with an absolute constant. -/
theorem sum_raddone_inv_pow_le {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ Finset.Icc 2 R,
        ((r : ℝ) + 1) / (p : ℝ) ^ r) ≤
      8 / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        (1 / (p : ℝ) ^ 2) *
          (((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hpPow : (2 : ℝ) ^ (r - 2) ≤ (p : ℝ) ^ (r - 2) := by
        gcongr
      have hrSplit : r = 2 + (r - 2) := by omega
      have hpowSplit : (p : ℝ) ^ r =
          (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
        conv_lhs => rw [hrSplit]
        rw [pow_add]
      rw [hpowSplit]
      have hnum : 0 ≤ (r : ℝ) + 1 := by positivity
      calc
        ((r : ℝ) + 1) /
              ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2)) ≤
            ((r : ℝ) + 1) /
              ((p : ℝ) ^ 2 * (2 : ℝ) ^ (r - 2)) := by
          gcongr
        _ = (1 / (p : ℝ) ^ 2) *
            (((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ 2) *
        (∑ r ∈ Finset.Icc 2 R,
          ((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ 2) * 8 :=
      mul_le_mul_of_nonneg_left (sum_shifted_linear_half_le_eight R)
        (by positivity)
    _ = 8 / (p : ℝ) ^ 2 := by ring



























end

end Erdos390.Full.LocalFugacityBounds

end

/- Source module: Erdos390.Full.PaperPrimePowerChamberError -/
section


/-!
# Explicit chamber-error majorants for prime-power aggregation

This file replaces the nested restoration ledger by one scalar remainder at
the natural product-reciprocal scale.  The scalar is explicit, uniform over
all moving primes and exponents, and retains the vanishing omitted-score and
`1 / log n` factors needed before the harmonic prime sum is taken.
-/

namespace Erdos390.Full.PaperPrimePowerChamberError

open ArithmeticModel Scale HeadPattern
open OmittedTiltPairChamber FullTiltPairChamber
open LocalFugacityBounds TwoLocalRestorationBound
open PaperTwoLocalRestorationBound PaperScaleMarkedCell
open FullTiltPrimePowerCovariance

noncomputable section



































/-- The reciprocal main term is controlled by the natural one-prime weight. -/
theorem abs_paperDivisibilityMain_pow_le_singleWeight
    {n p r : ℕ} (hn : 1 < n) (hp : Nat.Prime p)
    (hD4 : p ^ r ≤ yNat n ^ 4) :
    |paperDivisibilityMain n (p ^ r)| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r := by
  have hDpos : 0 < p ^ r := pow_pos hp.pos r
  have hraw := paperDivisibilityMain_nonneg_le hn hDpos hD4
  rw [abs_of_nonneg hraw.1]
  have hinv : 1 / (p : ℝ) ^ r ≤ singleWeight p r := by
    unfold singleWeight
    have hden : 0 ≤ (p : ℝ) ^ r := by positivity
    have hnum : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      nlinarith [show (0 : ℝ) ≤ r by positivity]
    exact div_le_div_of_nonneg_right hnum hden
  calc
    paperDivisibilityMain n (p ^ r) ≤
        1 / (DickmanBasic.rho DickmanBasic.U * (p ^ r : ℕ)) := hraw.2
    _ = (1 / DickmanBasic.rho DickmanBasic.U) *
        (1 / (p : ℝ) ^ r) := by
      norm_num only [Nat.cast_pow]
      ring
    _ ≤ (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r :=
      mul_le_mul_of_nonneg_left hinv
        (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)





end

end Erdos390.Full.PaperPrimePowerChamberError

end

/- Source module: Erdos390.Full.PaperRawTiltedValuationMeanRows -/
section


/-!
# Raw tilted full-valuation component-mean agreement

The common four-mark profile is summed only through
`Nat.log p (yNat n ^ 4)`.  The arbitrary-divisor fallback controls the
literal remaining valuation tail.  This produces the sharp
`epsilon(n)/p`, `epsilon(n) log L(n) -> 0` component-mean row needed for the
head nuisance coordinate.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperRawTiltedValuationMeanRows

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open StructuredCellValuationLaw ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPrimePowerFallback
open PaperPrimePowerChamberError PaperScaleMarkedCell
open FixedFiniteMixtureFullUniform FixedFiniteMixtureSignedSquarefree
open PaperPrimePowerAuxiliaryPrime PaperPrimePowerTailRate
open LocalFugacityBounds

noncomputable section

set_option maxHeartbeats 2400000



/-- The chamber single-prime weight has a uniform geometric sum beginning
at exponent one. -/
theorem sum_singleWeight_positiveExponents_le
    {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ positiveExponents R, singleWeight p r) ≤
      6 / (p : ℝ) := by
  by_cases hR : 1 ≤ R
  · have hset : positiveExponents R =
        insert 1 (Finset.Icc 2 R) := by
      ext r
      simp only [positiveExponents, Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    have htail := sum_raddone_inv_pow_le (p := p) (R := R) hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp0 : (0 : ℝ) < p := zero_lt_two.trans_le hpR
    have hsq : 8 / (p : ℝ) ^ 2 ≤ 4 / (p : ℝ) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hp0) hp0).2
      nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hpR)]
    calc
      singleWeight p 1 + ∑ x ∈ Finset.Icc 2 R, singleWeight p x =
          2 / (p : ℝ) +
            ∑ x ∈ Finset.Icc 2 R,
              (((x : ℝ) + 1) / (p : ℝ) ^ x) := by
        unfold singleWeight
        norm_num
      _ ≤ 2 / (p : ℝ) + 8 / (p : ℝ) ^ 2 :=
        add_le_add le_rfl htail
      _ ≤ 2 / (p : ℝ) + 4 / (p : ℝ) :=
        add_le_add le_rfl hsq
      _ = 6 / (p : ℝ) := by ring
  · have hR0 : R = 0 := by omega
    subst R
    simp [positiveExponents]
    positivity

variable {Cell : Type*} [Fintype Cell]



end

end Erdos390.Full.PaperRawTiltedValuationMeanRows

end

/- Source module: Erdos390.Full.PaperCanonicalMediumNuisanceRows -/
section


/-!
# Canonical raw-cell attachment for the medium nuisance rows

This file contains the dependent-type bookkeeping which identifies the
guard-deleted exponential tilt on a literal raw structured cell with the
`cellMediumLaw` carried by canonical `BridgeData`.  In particular, later
moving-prefix and prime-power estimates can be proved on the raw cell and
transported to the exact laws used by the nuisance Schur complement without
an unrecorded change of sample space.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus GuardedUniformCell ValuationScoreDomination

namespace FiniteProbability

variable {Alpha : Type*}

/-- Equality of the underlying finite sets, together with pointwise equality
of the scores and statistics, gives literal equality of tilted expectations.
The formulation is useful when the equality changes a subtype. -/
theorem uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq
    (S T : Finset Alpha) (hST : S = T)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (scoreS : S → ℝ) (scoreT : T → ℝ)
    (hscore : ∀ (x : S) (y : T), (x : Alpha) = (y : Alpha) →
      scoreS x = scoreT y)
    (F : Alpha → ℝ) :
    ((uniformOnFinset S hS).exponentialTilt scoreS).expect
        (fun x ↦ F (x : Alpha)) =
      ((uniformOnFinset T hT).exponentialTilt scoreT).expect
        (fun x ↦ F (x : Alpha)) := by
  subst T
  have hscoreEq : scoreS = scoreT := by
    funext x
    exact hscore x x rfl
  subst scoreT
  have hproof : hS = hT := Subsingleton.elim _ _
  subst hT
  rfl



end FiniteProbability

namespace PaperBridgeFit

open HeadPattern

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











end BridgeData

end PaperBridgeFit

end

end Erdos390.Full

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosure -/
section


/-!
# Sharp valuation-rate ingredients for the smooth source

This file begins the analytic lift left explicit by
`BankPaperCanonicalSmoothSourceGuardedRateClosure`.

The first theorem below is the sharp un-tilted full-valuation profile for one
fixed raw structured cell.  It is obtained only from already proved inputs:

* the common `paperDivisibilityMain` law through `yNat n ^ 4`;
* the arbitrary-divisor reciprocal fallback;
* the finite prime-power tail identity; and
* the sharp conversion of the `yNat n ^ 4` tail to `1 / (p * L n)`.

No full-valuation comparison is assumed.
-/

open Filter Topology
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PrimePowerCovariance
open Erdos390.Full.PrimePowerCutoffCovariance
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PaperMovingPrefixMarkedCell
open Erdos390.Full.PaperPrimePowerTailRate
open Erdos390.Full.PaperRawPrefixThirdCumulantFallback
open Erdos390.Full.PaperRawTiltedValuationMeanRows
open Erdos390.Full.LocalFugacityBounds
open Erdos390.Full.ValuationScoreDomination
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.GuardedUniformCell
open Erdos390.Full.GuardDeletionSquarefreeProfiles
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperCanonicalTiltedPrefixRows

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Fixed raw structured cells -/





/-! ## Literal guard deletion -/

/-- Tilting by the identically-zero score does not change an expectation.
This small identity lets the general conditional-deletion theorem be used
without replacing the literal uniform laws by unnamed equivalent laws. -/
theorem finiteProbability_exponentialTilt_zero_expect
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F : Omega → Real) :
    (mu.exponentialTilt (fun _ ↦ 0)).expect F = mu.expect F := by
  have hpartition :
      mu.expPartition (fun _ ↦ 0) = 1 := by
    unfold FiniteProbability.expPartition FiniteProbability.expect
    simp only [Real.exp_zero, mul_one]
    exact mu.mass_sum
  rw [mu.exponentialTilt_expect_eq, hpartition, div_one]
  apply congrArg mu.expect
  funext omega
  simp



/-! ## The concrete guard ledger at the stronger `1 / L` rate -/













/-- Bridge-data specialization of the preceding guarded raw-cell theorem.
The only additional input is the repository's literal identification of the
sample data with `canonicalSampleData`; no tilted law is introduced. -/
theorem
    exists_uniform_bridge_guardedCell_valuation_mean_profiles_paperRate
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData Head Band),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        (hsep : physicalBound (I.upper .minus) B.sampleData.n <
          physicalBound (I.lower .plus) B.sampleData.n) →
        (hremaining : ∀ c : Cell Head,
          (rawCell P I B.sampleData.n c \
            (G B.sampleData.n).guards).Nonempty) →
        B.sampleData = canonicalSampleData
          (W := B.sampleData.W) P I (G B.sampleData.n)
            hsep hremaining →
        ∀ p : BandPrime B.sampleData.n B.sampleData.W,
          let Kcut := Nat.log p.1 (yNat B.sampleData.n ^ 4)
          ∀ c : Cell Head,
            |(B.guardedCellProbability c).expect
                  (fun m ↦ valuation p.1 (m : Nat)) -
              ∑ k ∈ positiveExponents Kcut,
                paperDivisibilityMain B.sampleData.n (p.1 ^ k)| ≤
              Cval / ((p.1 : Real) * B.L) := by
  obtain ⟨Cval, hCval, N₀, hrate⟩ :=
    exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate
      P I Cprom Cbank G W hW hHeadLe
  refine ⟨Cval, hCval, N₀, ?_⟩
  intro Band _instBand _instBandDec B hN hBW hsep hremaining hcanonical p
  have hrateP :=
    hrate (n := B.sampleData.n) (p := p.1) hN
      (by simpa only [hBW] using p.2)
  dsimp only at hrateP ⊢
  intro c
  have hraw := hrateP c (hremaining c)
  have hcell :
      B.sampleData.cellFinset c =
        rawCell P I B.sampleData.n c \
          (G B.sampleData.n).guards := by
    calc
      B.sampleData.cellFinset c =
          (canonicalSampleData (W := B.sampleData.W)
            P I (G B.sampleData.n) hsep hremaining).cellFinset c :=
        congrArg (fun D : StructuredSampleData Head ↦ D.cellFinset c)
          hcanonical
      _ = rawCell P I B.sampleData.n c \
          (G B.sampleData.n).guards := by
        exact canonicalSampleData_cellFinset
          P I (G B.sampleData.n) hsep hremaining c
  have hreindex :
      (uniformOnFinset
          (rawCell P I B.sampleData.n c \
            (G B.sampleData.n).guards)
          (hremaining c)).expect
            (fun m ↦ valuation p.1 (m : Nat)) =
        (uniformOnFinset
          (B.sampleData.cellFinset c)
          (B.sampleData.cell_nonempty c)).expect
            (fun m ↦ valuation p.1 (m : Nat)) := by
    have htilt :=
      uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq
        (rawCell P I B.sampleData.n c \
          (G B.sampleData.n).guards)
        (B.sampleData.cellFinset c) hcell.symm
        (hremaining c) (B.sampleData.cell_nonempty c)
        (fun _ ↦ (0 : Real)) (fun _ ↦ (0 : Real))
        (by
          intro x y hxy
          rfl)
        (fun m : Nat ↦ valuation p.1 m)
    simpa only [finiteProbability_exponentialTilt_zero_expect] using htilt
  unfold BridgeData.guardedCellProbability
  rw [← hreindex]
  simpa only [BridgeData.L, Erdos390.Full.Scale.L, hBW] using hraw

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightEventualSupplierConnector -/
section


/-!
# Honest reduction boundary for the fresh Section 9 post-height bridge

This file deliberately stops before the synchronized analytic completion.
It exports three narrower layers:

* the uniform guarded zero-cell valuation estimate which was previously
  buried inside the placement proof;
* the genuinely missing post-height target/source producer obligation; and
* a finite local-input reduction which packages already-produced analytic
  fields without calling that package a completed eventual supplier.

The selector constant is chosen by
`exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate`
before Proposition 8.7 chooses its radius and `Cpost`.  In particular, no
supplier is asked to work for every possible later `Cinitial`.

Every family-level definition below uses one
`BankPaperCanonicalGuardedTailFamily`, hence one realization and guarded
certificate at a given index.  The public bridge is always the literal
fresh bridge `J.postHeightBridge`; no legacy symmetric-height equality
`q = q0` occurs.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.DickmanBasic
open Erdos390.Full.FiniteProbability
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperPrimePowerChamberError
open Erdos390.Full.PaperRawTiltedValuationMeanRows
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Uniform zero-cell valuation means -/

/-- Uniform paper-rate upper bound for both guarded zero-cell valuation
means.  This is the direct one-sided consequence of the canonical guarded
cell profile estimate used by the Section 9 placed-selector theorem. -/
theorem
    exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W) :
    ∃ Azero : Real, 0 < Azero ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        (hsep : physicalBound (I.upper .minus) B.sampleData.n <
          physicalBound (I.lower .plus) B.sampleData.n) →
        (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
          (rawCell Patterns I B.sampleData.n cell \
            (G B.sampleData.n).guards).Nonempty) →
        B.sampleData =
          canonicalSampleData
            (W := B.sampleData.W) Patterns I
              (G B.sampleData.n) hsep hremaining →
        ∀ p : BandPrime B.sampleData.n B.sampleData.W,
          ∀ sigma : PhysicalSign,
            (B.guardedCellProbability (none, sigma)).expect
                (fun m ↦ valuation p.1 (m : Nat)) ≤
              Azero / (p.1 : Real) := by
  obtain ⟨Ccell, hCcell, Ncell, hcellProfile⟩ :=
    exists_uniform_bridge_guardedCell_valuation_mean_profiles_paperRate
      Patterns I Cprom Cbank G W hW hHeadLe
  let Amain : Real := 6 / rho DickmanBasic.U
  let Azero : Real := Amain + Ccell
  have hAmain : 0 < Amain := by
    dsimp only [Amain]
    exact div_pos (by norm_num) DickmanBasic.rho_U_pos
  have hAzero : 0 < Azero := by
    dsimp only [Azero]
    exact add_pos hAmain hCcell
  have hLtendsto : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogEvent : ∀ᶠ n : Nat in atTop, 1 ≤ L n :=
    hLtendsto.eventually (eventually_ge_atTop 1)
  obtain ⟨Nlog, hNlog⟩ := Filter.eventually_atTop.mp hlogEvent
  refine ⟨Azero, hAzero, max 2 (max Ncell Nlog), ?_⟩
  intro Band _instBand _instBandDec B hN hBW hsep hremaining
    hcanonical p sigma
  have hn : 1 < B.sampleData.n := by omega
  have hNcell : Ncell ≤ B.sampleData.n := by omega
  have hNlogBound : Nlog ≤ B.sampleData.n := by omega
  have hp := prime_of_mem_primeBand p.2
  have hpR : 0 < (p.1 : Real) := by exact_mod_cast hp.pos
  have hLone : 1 ≤ B.L := by
    simpa only [BridgeData.L] using
      hNlog B.sampleData.n hNlogBound
  have hcellRaw :=
    hcellProfile B hNcell hBW hsep hremaining hcanonical p
  let Kcut := Nat.log p.1 (yNat B.sampleData.n ^ 4)
  let mainSum := ∑ k ∈ positiveExponents Kcut,
    paperDivisibilityMain B.sampleData.n (p.1 ^ k)
  have hpY : p.1 ≤ yNat B.sampleData.n :=
    le_yNat_of_mem_primeBand p.2
  have hY4pos : 0 < yNat B.sampleData.n ^ 4 :=
    pow_pos (hp.pos.trans_le hpY) 4
  have hpK : p.1 ^ Kcut ≤ yNat B.sampleData.n ^ 4 := by
    dsimp only [Kcut]
    exact Nat.pow_log_le_self p.1 hY4pos.ne'
  have hmainTerm (k : Nat) (hk : k ∈ positiveExponents Kcut) :
      0 ≤ paperDivisibilityMain B.sampleData.n (p.1 ^ k) ∧
        paperDivisibilityMain B.sampleData.n (p.1 ^ k) ≤
          (1 / rho DickmanBasic.U) * singleWeight p.1 k := by
    have hkLe : k ≤ Kcut := (mem_positiveExponents.mp hk).2
    have hpk :
        p.1 ^ k ≤ yNat B.sampleData.n ^ 4 :=
      (Nat.pow_le_pow_right hp.pos hkLe).trans hpK
    have hraw :=
      paperDivisibilityMain_nonneg_le hn (pow_pos hp.pos k) hpk
    refine ⟨hraw.1, ?_⟩
    have habs :=
      abs_paperDivisibilityMain_pow_le_singleWeight hn hp hpk
    simpa only [abs_of_nonneg hraw.1] using habs
  have hweight :
      (∑ k ∈ positiveExponents Kcut, singleWeight p.1 k) ≤
        6 / (p.1 : Real) :=
    sum_singleWeight_positiveExponents_le hp.two_le
  have hmainUpper : mainSum ≤ Amain / (p.1 : Real) := by
    calc
      mainSum ≤
          ∑ k ∈ positiveExponents Kcut,
            (1 / rho DickmanBasic.U) * singleWeight p.1 k := by
        dsimp only [mainSum]
        exact Finset.sum_le_sum fun k hk => (hmainTerm k hk).2
      _ = (1 / rho DickmanBasic.U) *
          ∑ k ∈ positiveExponents Kcut, singleWeight p.1 k := by
        rw [Finset.mul_sum]
      _ ≤ (1 / rho DickmanBasic.U) * (6 / (p.1 : Real)) := by
        exact mul_le_mul_of_nonneg_left hweight
          (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)
      _ = Amain / (p.1 : Real) := by
        dsimp only [Amain]
        field_simp [hpR.ne', DickmanBasic.rho_U_pos.ne']
  let mean :=
    (B.guardedCellProbability (none, sigma)).expect
      (fun m ↦ valuation p.1 (m : Nat))
  have hprofile :
      |mean - mainSum| ≤ Ccell / ((p.1 : Real) * B.L) := by
    simpa only [mean, Kcut, mainSum] using
      hcellRaw (none, sigma)
  have herror :
      Ccell / ((p.1 : Real) * B.L) ≤
        Ccell / (p.1 : Real) := by
    apply div_le_div_of_nonneg_left hCcell.le hpR
    calc
      (p.1 : Real) = (p.1 : Real) * 1 := by ring
      _ ≤ (p.1 : Real) * B.L :=
        mul_le_mul_of_nonneg_left hLone hpR.le
  have hmeanLe :
      mean ≤ mainSum + Ccell / ((p.1 : Real) * B.L) := by
    have hself : mean - mainSum ≤ |mean - mainSum| :=
      le_abs_self _
    linarith
  calc
    mean ≤ mainSum + Ccell / ((p.1 : Real) * B.L) := hmeanLe
    _ ≤ Amain / (p.1 : Real) + Ccell / (p.1 : Real) :=
      add_le_add hmainUpper herror
    _ = Azero / (p.1 : Real) := by
      dsimp only [Azero]
      ring

/-! ## The genuine producer obligation -/





/-!
## Exact dependent-field census

For `BankPaperCanonicalSectionNinePostHeightDependentInputsAt`, the current
producer map is:

* the physical part of the fresh target interior:
  `bankPaperCanonicalSectionEight_physicalMeanError_isBigO` after the
  Section 8 family identities are synchronized; the unproved part of the
  coherent target constructor is the fixed head-simplex reserve and its
  assembly with that physical interval;
* `Cinitial`, its nonnegativity, and `selectorDeficit`: the uniform placed
  selector theorem, using the zero-cell theorem exported above together
  with the Section 8 `d` and final-mass rates;
* the balanced-alpha box: the standalone eventual balanced-alpha theorem;
* `Cfixed`, `roundedFrozenLedger`, and `fixedRoom`: choose
  `Cfixed = betaProt + Cactive`; additive-placement frozen invariance and
  post-height rounded-source invariance give the pointwise ledger;
* `primeDeviation`: eventual canonical `MomentReady` followed by
  `actual_L1_bound_of_ready`;
* `radius` and `localP87`: varying-active-mass canonical Proposition 8.7,
  with `Ctarget = 7 * Cinitial`, `Cmass = 1`, and
  `Cactive = S.Cmass / S.density`;
* `cellIndex`: the literal `bankPaperCanonicalRatioCellIndex`;
* `W_large`: the fixed choice `2 ≤ W`;
* `sigma_nonneg` and `sigma_le_betaProt`: the fixed parameter choice;
* `largeL`: `eventually_canonical_exponential_slack_le_L`, with `sigma`
  absorbed into the fixed term; and
* `nonsmooth`: `eventually_roughCanonicalBalancedNonsmoothBounds`.

The target envelope, placed frozen ledger, active ledger, active-seed bound,
and protected reserve are not fields of the dependent record: the existing
post-height local connector constructs them after the above data are
installed.

Thus the only producer gap is the uniform coherent target/source
construction recorded in
`BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt`.
-/

/-! ## Non-final finite local-input reduction -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal007_004.{u_1} := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate
