-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_uniform_sectionNinePostHeightPlacementValuationMoment_paperRate_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:30:03.477204+00:00
-- url     : https://prove2.me/submissions/00f8f85a-6fe6-4972-b7df-cb77aaf44ccd

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
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_roundedActive_sub_guardedBase




section
universe u_1
theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate : Erdos390.RemainingAnalyticGoal007_013.{u_1} := @Erdos390.WholePaper.BankPaperRealization.exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate : Erdos390.RemainingAnalyticGoal007_006 := @Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate_compact
end
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

/- Source module: Erdos390.Full.UniformFiniteProbability -/
section


/-!
# Uniform probability on an actual finite cell

This is the exact bridge between counting averages on a finite arithmetic
cell and the `FiniteProbability` objects used by the tilt and covariance
modules.  Nonemptiness is explicit, so normalization never divides by a
silently vanishing cell cardinality.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Alpha : Type*}





/-- Expectation under the uniform law is the literal subtype sum divided by
the actual cell cardinality. -/
theorem uniformOnFinset_expect_eq (S : Finset Alpha) (hS : S.Nonempty)
    (F : S → ℝ) :
    (uniformOnFinset S hS).expect F =
      (∑ x : S, F x) / (S.card : ℝ) := by
  unfold expect
  calc
    (∑ x : S, (1 / (S.card : ℝ)) * F x) =
        (1 / (S.card : ℝ)) * ∑ x : S, F x := by
      rw [Finset.mul_sum]
    _ = (∑ x : S, F x) / (S.card : ℝ) := by ring

/-- Subtype summation is exactly the usual filtered finset summation. -/
theorem sum_subtype_eq_sum_filter (S : Finset Alpha) (F : Alpha → ℝ) :
    (∑ x : S, F x) = ∑ x ∈ S, F x := by
  exact Finset.sum_coe_sort S F

/-- Expectation written with the ambient function and the literal cell
cardinality. -/
theorem uniformOnFinset_expect_ambient_eq
    (S : Finset Alpha) (hS : S.Nonempty) (F : Alpha → ℝ) :
    (uniformOnFinset S hS).expect (fun x : S ↦ F x) =
      (∑ x ∈ S, F x) / (S.card : ℝ) := by
  rw [uniformOnFinset_expect_eq, sum_subtype_eq_sum_filter]

end FiniteProbability

end

end Erdos390.Full

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

/- Source module: Erdos390.WholePaper.UpperScale -/
section


/-!
# Elementary scale facts for the upper bound

This module isolates the exact ceiling and endpoint used on the upper-bound
side of the paper.  Every asymptotic statement is proved directly from
elementary real-logarithm limits.  No prime-counting input is used.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section









/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightLedger -/
section


/-!
# The exact smooth-row quota and height ledger from Section 8

This file records the algebraic part of the paper's smooth-row initialization
without replacing any actual finite mass by an asymptotic main term.

The literal active base component is the constant weight `betaAct / L n` on
the head-free, `yNat n`-smooth part of the broad interval.  Its exact support
is the complete-rough row with label one.  The later definitions follow the
paper verbatim:

* `Q_sm(0)` is the nearest integer to `m_sm,fr + qTilde`, with a half-integer
  tie sent to the smaller integer;
* `q0 = Q_sm(0) - m_sm,fr`;
* `Q_sm(d) = Q_sm(0) - d` and `qAct(d) = q0 - d`;
* `A0 = logY - Lambda0 - q0 * L` and `A(d) = A0 + d * L`;
* `d` is the tie-lower nearest integer to
  `(mu * q0 - A0) / (L + mu)`.

All displayed identities and the two nearest-integer errors are unconditional.
The analytic comparison between the raw base mass and the actual post-guard
mass is deliberately left to the companion asymptotic module.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal rough smooth base component -/

















/-! ## Tie-lower nearest integers -/









/-- The universal half-unit rounding error. -/
theorem bankPaperNearestIntegerTieLower_abs_sub_le (x : Real) :
    |(bankPaperNearestIntegerTieLower x : Real) - x| ≤ 1 / 2 := by
  have hcell :=
    (bankPaperNearestIntegerTieLower_eq_iff x
      (bankPaperNearestIntegerTieLower x)).1 rfl
  apply abs_le.mpr
  constructor <;> linarith

/-! ## Exact smooth-row quota initialization -/







/-- Exact expression for the initialization error. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_sub_actual
    (mFrozen qTilde : Real) :
    bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde =
      (bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
        (mFrozen + qTilde) := by
  unfold bankPaperCanonicalSmoothInitialActiveMass
  ring

/-- The paper's literal bound `|q0 - qTilde| <= 1/2`. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen qTilde : Real) :
    |bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde| ≤
      1 / 2 := by
  rw [bankPaperCanonicalSmoothInitialActiveMass_sub_actual]
  exact bankPaperNearestIntegerTieLower_abs_sub_le (mFrozen + qTilde)

















/-! ## Exact frozen-height ledger and centered adjustment -/



























/-! ## Literal Section 8 families -/

























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger -/
section


/-!
# Guard-local canonical rough-row ledger

This module isolates the finite bookkeeping that occurs when the paper
passes from the raw canonical rough candidates to the candidates left after
the numerical guards

`Gamma_num = anchors ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Only literal finite-set identities are proved here.  In particular, this
file does **not** assume or assert a local guard census, a lower bound for a
guarded broad pool, or enough guarded-row capacity for a corrected selector.
Those still-missing estimates are exposed at the end as named propositions.

The postcharge target is kept in `Real` form for the correction algebra and
in `Int` form for its exact integrality witness.  Its nonnegativity is a
finite consequence of the actual donor/base row-preserving bijection and of
the disjoint upper-tail backing of the fixed exceptional factors and donors.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Literal guarded candidates and row pieces -/













theorem roughCanonicalGuardedCandidateSet_disjoint_guardSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) :
    Disjoint
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (R.roughCanonicalGuardSet certificate deltaStar) := by
  exact Finset.sdiff_disjoint













/-! ## The donor/base row-preserving bijection -/









/-! ## Upper-tail ownership and the postcharge target -/





























/-! ## Exact local discrepancy ledger -/







/-! ## Exact support reduction for the local deletion set -/







/-! ## Explicit remaining finite/analytic obligations -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperProposition87ActualDataConnector -/
section


/-!
# Actual paper data at the Proposition 8.7 / guarded-selector interface

The paper does not use the mass-one normalization of the bridge.  Its
literal active weights are the numbers `z_m^0`, and

`q_n = sum_m z_m^0`.

At a clean numerical coordinate the protected frozen layer may overlap the
active layer.  Consequently `q_n` is not, in general, the sum of the whole
guarded selector on the active support.  This module keeps the two layers
separate.  Every guarded candidate is represented by a frozen tag of weight

`preSelector a - activeSeedAmbient a`,

while Proposition 8.7 evolves the active seed.  Thus the protected overlap
is retained exactly and the combined selector at time zero is the supplied
guarded pre-selector.

The single construction still missing from the finite guarded ledger is
named `BankPaperCanonicalActualActiveMeasureConstructor`.  It asks only for
the paper's active-measure realization: the seed has the canonical
barycentric shape, has eventual paper-scale mass at least one, is supported
on the guarded candidates, and is dominated by the already feasible
pre-selector.  Row integrality, target agreement, band balance, support,
pointwise estimates, and prefix estimates are not repeated in this
constructor; they are derived below from the existing guarded selector and
the Proposition 8.7 path.
-/

open Filter Topology Set
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## The literal active mass and its sole construction socket -/

























/-! ## The actual scaled bridge data -/









/-! ## Tagged frozen remainder and exact push-forward -/





















/-! ## The initial combined selector -/









/-! ## The literal active marked target and endpoint -/













/-! ## Smooth active support and unchanged complete-rough rows -/









/-- The active seed push-forward vanishes at a coordinate which is not the
value of any active sample tag. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (a : Nat) (ha : forall m : D.Sample, D.value m ≠ a) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a = 0 := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_eq_zero
  intro m _hm
  rw [if_neg (ha m)]













/-! ## Prime support, exact bands, and the derived prefix ledger -/











/-! ## Complete endpoint handoff -/



/-! ## Direct coupling to the guarded continuation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic -/
section


/-!
# The analytic Section 8 smooth-row quota and height bridge

The raw active smooth component from the exact companion file has a positive
`n / log n` lower bound by the repository's uniform de Bruijn--Saias and
fixed-head estimates.  This file proves that bound directly for complete-
rough label one, then propagates it through the exact nearest-integer and
height-center constructions.

Only one repository-level analytic ledger remains absent.  It is named
`BankPaperCanonicalSectionEightAnalyticLedger` below and contains exactly:

* the actual post-guard smooth mass differs from the explicit raw base mass
  by `o(n / log n)`;
* the literal frozen height defect `A0` is `O(n / log n)`.

These are precisely the two estimates asserted together in the paper's
Section 8 frozen ledger.  No selector, active-measure, or positivity premise
is hidden in that predicate.  Every consequence after it, including
`d = O(n / log^2 n)` and the positive lower bound for `q0 - d`, is proved
here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The label-one raw base pool is macroscopically large -/











/-! ## The exact missing analytic ledger -/



/-! ## Nearest-integer initialization preserves the paper scale -/











/-! ## The logarithmically smaller height adjustment -/

/-- The paper's scale `n / log^2 n` tends to infinity. -/
theorem secondOrderScale_div_L_tendsto_atTop :
    Tendsto (fun n : Nat => secondOrderScale n / L n) atTop atTop := by
  have hzero : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (nhds 0) := by
    simpa only [L, Function.comp_apply, id_eq] using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := Real))).tendsto_div_nhds_zero
  have hpos : ∀ᶠ n : Nat in atTop,
      0 < L n ^ 2 / (n : Real) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (pow_pos (L_pos hn) 2) (by positivity)
  have hright : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hnReal : (n : Real) ≠ 0 := by positivity
  apply (eq_div_iff hL.ne').2
  change (L n ^ 2 / (n : Real))⁻¹ * L n = (n : Real) / L n
  rw [inv_div]
  field_simp [hL.ne', hnReal]





/-! ## Full propagation from the minimal missing ledger -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothProtectedAdditiveRefinement -/
section


/-!
# Additive protected refinement on the guarded smooth broad pool

The literal raw selector already has constant broad weight `beta / L`.
The paper splits `beta = betaProt + betaAct`, freezes the first summand,
and replaces the second by the structured active seed.  The earlier
guarded continuation records only the resulting smooth-row integer quota;
it does not retain this pointwise additive identity.

This file restores that identity by an explicit local refinement.  On the
guarded smooth broad pool it sets

`preSelector = betaProt / L + activeSeedAmbient`,

and away from that pool it leaves an already constructed base selector
unchanged.  Thus nonsmooth corrected rows are untouched, while the actual
frozen remainder is definitionally the protected constant `betaProt / L`.
The existing raw-point theorem proves that this constant is precisely the
protected part of the paper's head-compatible raw broad weight.

This closes the positive-remainder and pre-selector-upper algebra without a
new selector assumption.  It deliberately does not claim that replacing an
arbitrary smooth row preserves its integer quota or prime moments: those are
the separate smooth-ledger/active-measure construction obligations.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The explicit protected layer and additive refinement -/









/-- On the clean smooth broad pool, the explicit protected layer is exactly
the paper's head-compatible raw weight with broad parameter `betaProt`. -/
theorem bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha betaProt : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
        deltaStar betaProt a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L a := by
  rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
    B R certificate ha]
  exact (roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
    (R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
      certificate deltaStar B.sampleData.W K 1 ha)).symm

















/-! ## Derived active and pre-selector upper bounds -/









/-! ## Exact protected window and actual endpoint -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothAdditivePlacement -/
section


/-!
# Paper-faithful placement boundary for the guarded smooth refinement

The smooth bridge in the paper does not preserve the medium-prime moments
of an earlier provisional selector.  It freezes the protected layer,
redistributes the active mass while preserving the smooth-row ledger and
the moments outside the tangent band, and then fits the medium-prime band
moments.  Proposition 8.7 supplies that latter fit.

Accordingly, the pre-selector part of the actual endpoint theorem needs
only complete-row integrality and deficit support outside the medium-prime
band.  Its older statement accepted a full rounded-selector tangent input,
although the proof used only those two fields.  This file records the
weaker exact theorem, constructs the minimized ledger from the paper's two
literal zero-head cells, and proves the exact scaled structured head-cell
moments.  It then resolves the support boundary--the nonzero head cells lie
in the smooth row, not in its head-free correction subpool--by transporting
a signed ledger over the whole smooth row for the corrected selector.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization



/-! ## Exact finite algebra for the two zero-head pools -/





















/-! ## The head-free correction-pool ledger -/











/-! ## Structured head-cell realization -/





/-- Weighted ambient push-forward over a support containing all structured
values is exactly the corresponding tagged weighted sum. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (support : Finset Nat)
    (hvalues : forall m : D.Sample, D.value m ∈ support)
    (p : Nat) :
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight D seed a *
          valuation p a) =
      ∑ m : D.Sample, seed m * valuation p (D.value m) := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalues m)).elim













/-! ## Exact support boundary -/



/-! ## Signed whole-smooth-row placement ledger -/



































end BankPaperRealization

/-! ## Weaker actual-endpoint preselector interface -/



namespace BankPaperRealization







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalMediumPrimeStructuredPlacementMomentRateConnector -/
section


/-!
# Medium-prime rate for the structured two-zero-cell placement moment

The literal two-zero-cell rebalance spreads each requested mass uniformly
inside one guarded structured cell.  Consequently its medium-prime moment is
controlled by the valuation mean of the *uniform guarded-cell law*.  It is not
unconditionally controlled for arbitrary `minusMass` and `plusMass`, and the
uniform law must not be silently replaced by the generally tilted
`cellMediumLaw`.

This connector first proves the exact finite expectation identity.  It then
combines:

* a reciprocal valuation-mean bound in each of the two zero-head cells; and
* an `O(secondOrderScale / L)` bound for the sum of the absolute mass changes.

The resulting estimate is exactly on the
`secondOrderScale / (p * L)` scale required by the third conjunct of
`BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Exact uniform-cell expectation algebra -/

/-- A uniform mass increment in one structured cell has valuation moment
equal to the requested mass times the valuation expectation under the
literal uniform guarded-cell probability. -/
theorem
    sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (cell : Cell Head)
    (mass : Real) (p : Nat) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalUniformCellIncrement
            B.sampleData cell mass m *
          valuation p (B.sampleData.value m)) =
      mass * (B.guardedCellProbability cell).expect
        (fun m ↦ valuation p (m : Nat)) := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single cell]
  · simp only [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, if_true, StructuredSampleData.value,
      Fintype.card_coe]
    unfold BridgeData.guardedCellProbability
    rw [Erdos390.Full.FiniteProbability.uniformOnFinset_expect_eq]
    rw [← Finset.mul_sum]
    ring
  · intro other _hother hne
    apply Finset.sum_eq_zero
    intro m _hm
    simp [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, hne]
  · intro hnot
    exact (hnot (Finset.mem_univ cell)).elim



/-! ## Quantitative paper-rate closure -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenImplementationRateReductionConnector -/
section


/-!
# Literal implementation-rate reductions for the rounded frozen-top source

The balanced selector-deficit identity for the rounded frozen-top source
contains three implementation terms.  This file connects each of them to
the strongest already justified finite reduction, without identifying the
frozen-top source with the older no-top source.

* The source-to-guarded defect is partitioned into complete rough rows.
  Every nonsmooth row cancels for the literal frozen-top selector, leaving
  exactly one guarded smooth-row defect.
* The guarded/raw defect is source-independent, so its existing rowwise
  pool-moment and numerator-shift majorant applies literally.
* A second two-zero-cell rebalance has the existing uniform-cell valuation
  moment whenever the retained outside part of the frozen-top source agrees
  with its old tagged seed on occupied active coordinates.  That compatibility
  is stated explicitly; it is not inferred by confusing the top source with
  the legacy source.

The only quantitative inputs left by the final constructor are therefore
the smooth-row mismatch, the guarded/raw rowwise majorant, the two uniform
cell valuation means, and the absolute two-cell mass budget.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Source-parametric nonsmooth cancellation -/













/-! ## Literal rounded frozen-top source reduction -/









/-! ## The two literal non-placement defect inputs -/







/-! ## Source-parametric two-zero placement moment -/





/-! ## Literal frozen-top placement specialization -/





/-- Vanishing of the restored top weight supplies the exact outside
compatibility, by unfolding the label-one branch on the guarded smooth row. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_topInvisible
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (htop :
      BankPaperCanonicalTopFrozenSmoothTopInvisibleOnStructuredActive
        (K := K) B R certificate deltaStar alpha) :
    BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
      (K := K) B R certificate T deltaStar betaProt alpha beta qTilde := by
  intro a haActive haNotPool
  have haRow := hactiveSmooth haActive
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1 :=
    (mem_completeRoughRowFiber.mp haRow).2
  unfold bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop
  rw [if_pos haLabel, htop a haActive haNotPool]
  ring





/-! ## Complete three-input constructor -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenSmoothFeasibilityConnector -/
section


/-!
# Smooth-row feasibility for the frozen-top source

The classification theorem for the frozen-top source leaves one local
premise on complete rough label `1`.  This file discharges that premise for
the literal scaled active seed.

There are two elementary points.

* At a surviving smooth coordinate in the broad lower block, the protected
  layer is exactly the raw head-compatible weight.  If the coordinate is
  head-free it lies in the guarded smooth correction pool; otherwise both
  weights vanish.
* Away from the structured active image the ambient scaled seed vanishes.
  On the image, the existing
  `BankPaperCanonicalStructuredAdditivePlacementCapacity` is precisely the
  required upper bound.

Thus the only geometric input is that the structured active values lie in
the broad lower block.  This is the finite form of the strict physical
upper-endpoint gap already used in the canonical Section 8 geometry.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Broad support from the physical endpoint gap -/



/-! ## Identification of the protected layer on the broad smooth row -/

/-- On every surviving smooth-row coordinate in the broad lower block, the
explicit protected layer equals the raw head-compatible weight with broad
parameter `betaProt`.

The existing pointwise theorem handles the head-free case.  In the
non-head-free case the coordinate is outside the correction pool and both
sides are zero. -/
theorem
    bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha betaProt : Real} {a : Nat}
    (haSmooth :
      a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (haBroad :
      a ∈ roughBroadLowerBlock B.sampleData.n
        (upperTailLength c B.sampleData.n) K) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
        B R certificate deltaStar betaProt a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L a := by
  by_cases hcop : Nat.Coprime a (roughHeadModulus B.sampleData.W)
  · have haCandidate :
        a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K :=
      (mem_completeRoughRowFiber.mp haSmooth).1
    have haSurvives :
        a ∉ R.roughCanonicalGuardSet certificate deltaStar :=
      (Finset.disjoint_left.mp
        (R.roughCanonicalGuardedCandidateSet_disjoint_guardSet
          certificate deltaStar K)) haCandidate
    have haRawPool :
        a ∈ roughCanonicalBroadCorrectionPool B.sampleData.W
          B.sampleData.n (upperTailLength c B.sampleData.n) K
            (yNat B.sampleData.n) 1 := by
      apply mem_completeRoughRowFiber.mpr
      exact
        ⟨mem_roughHeadFree.mpr ⟨haBroad, hcop⟩,
          (mem_completeRoughRowFiber.mp haSmooth).2⟩
    have haPool :
        a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      rw [roughCanonicalGuardedBroadCorrectionPool, Finset.mem_sdiff]
      exact ⟨haRawPool, haSurvives⟩
    exact
      bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem
        B R certificate haPool
  · have hnotPool :
        a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      intro haPool
      have haRawPool :=
        R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
          certificate deltaStar B.sampleData.W K 1 haPool
      have haHeadFree :=
        (mem_completeRoughRowFiber.mp haRawPool).1
      exact hcop (mem_roughHeadFree.mp haHeadFree).2
    rw [
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
        B R certificate hnotPool]
    simp [roughHeadCompatibleRawWeight, hcop]

/-! ## The atomic smooth-row premise -/



/-! ## Full finite feasibility -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourcePrebridgeConnector -/
section


/-!
# The literal frozen-top source-to-post-height prebridge

The frozen-top rounded source contains its own nearest-integer active seed,
whereas the final baseline uses the fresh post-height barycentric seed of
mass `q0-d`.  These seeds are not equal.  What the structured prebridge
needs is instead their exact *signed difference* on the complete smooth
row:

* its total mass is the integer `-d`;
* its valuation moment at every head prime is zero.

This file proves that ledger.  The old head moment is recovered from the
literal source state's zero deficit outside the medium-prime band and the
paper's selector-tail target.  The new head moment is the exact
`activeHeadTarget` realized by the post-height target.  Thus no equality of
the old and new seeds is assumed.

The final theorem combines this ledger with the geometric feasibility
theorem from the post-height placed-measure connector, yielding the actual
measure and the full row-integral structured placement.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

namespace BankPaperRealization

/-! ## The geometric outside compatibility -/

/-- Broad-lower-block support makes the restored smooth top invisible at
every occupied structured coordinate outside the protected pool.  Hence
the literal rounded frozen-top source has the exact outside compatibility
needed for active-seed replacement.

This discharges the earlier compatibility predicate from concrete support
geometry rather than retaining it as an abstract contract. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K) :
    BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
      (K := K) B R certificate Tsource deltaStar betaProt
        alpha beta qTilde := by
  apply
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_topInvisible
      (K := K) B R certificate Tsource deltaStar betaProt alpha beta qTilde
        hactiveSmooth
  intro a haActive haNotPool
  obtain ⟨m, rfl⟩ :=
    mem_bankPaperCanonicalStructuredActiveValues.mp haActive
  have hmActive :
      B.sampleData.value m ∈
        bankPaperCanonicalStructuredActiveValues B.sampleData :=
    mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩
  have hmSmooth := hactiveSmooth hmActive
  calc
    bankPaperCanonicalSmoothTopWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha B.L
          (B.sampleData.value m) =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L
          (B.sampleData.value m) :=
      bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
        B R certificate hmSmooth haNotPool
    _ =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
        B R certificate deltaStar betaProt
          (B.sampleData.value m) :=
      (bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
        B R certificate hmSmooth (hactiveBroad m)).symm
    _ = 0 :=
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
        B R certificate haNotPool

/-! ## Arbitrary replacement of a two-zero-cell source seed -/

/-- Pointwise signed identity for replacing the active seed of an arbitrary
two-zero-cell source by a fresh structured seed.

The outside selector may retain any frozen data.  It is constrained only
at occupied active coordinates outside the protected broad pool, exactly
as in the existing two-zero-cell placement theorem. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed newSeed : B.sampleData.Sample → Real)
    (outsideSelector : Nat → Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData →
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 →
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a)
    (a : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt
          (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector)
          newSeed a -
        bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData newSeed a -
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        newSeed hactive]
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
          B R certificate hpool]
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_pos hpool]
      ring
    · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
          B R certificate hpool]
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_neg hpool, houtsideActive a hactive hpool]
      ring
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        newSeed hactive]
    have hnew :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData newSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have hold :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
          B R certificate
            (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed outsideSelector)
            newSeed hpool]
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_pos hpool, hnew, hold]
      ring
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
          B R certificate
            (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed outsideSelector)
            newSeed hpool,
        hnew, hold]
      ring



/-! ## Recovering the old head moment from the literal source state -/



/-! ## The paper's `q0-d` prebridge ledger -/



/-! ## Row quota and full placement -/





/-! ## One-shot geometric source-to-post-height construction -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedRateClosure -/
section


/-!
# Exact reduction of the smooth source-to-guarded rate

The literal frozen-top implementation defect has already been reduced to
complete rough label `1`.  This file exposes the finite algebra inside that
last row.

There are two points which are easy to conflate.

* The paper's `qTilde` is the mass of the guarded active broad layer.  When
  the canonical scaled seed is instantiated at that mass, its literal mass
  is *exactly* the guarded smooth base mass.  No asymptotic comparison is
  needed.
* The valuation moment is not determined by total mass.  After the exact
  mass synchronization, the remaining analytic term is the difference
  between the scaled barycentric valuation moment and the uniform guarded
  broad-pool valuation moment.  The nearest-integer normalization contributes
  only the two explicit zero-head-cell moments.

The declarations below prove only these exact reductions.  In particular,
no `O(1 / (p L))` valuation comparison is introduced as an assumption.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.StructuredCells

noncomputable section

namespace BankPaperRealization

/-! ## Exact moving structured-cell identification -/





/-! ## Exact guarded-mass synchronization -/



/-! ## The three literal valuation moments -/







/-- The rounded active valuation moment is exactly the scaled moment plus
the two displayed zero-cell moments. -/
theorem
    sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_valuation_eq_scaled_add_nearestInteger
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha qTilde : Real) (p : Nat) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m *
          valuation p (B.sampleData.value m)) =
      bankPaperCanonicalScaledActiveValuationMoment T qTilde p +
        bankPaperCanonicalTopFrozenNearestIntegerValuationMoment (K := K)
          B R certificate deltaStar betaProt alpha qTilde p := by
  unfold bankPaperCanonicalScaledActiveValuationMoment
  unfold bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
  unfold bankPaperCanonicalTopFrozenRoundedActiveSeed
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde) m *
          valuation p (B.sampleData.value m)) =
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalScaledActiveSeed T qTilde m *
            valuation p (B.sampleData.value m)) +
        (∑ m : B.sampleData.Sample,
          bankPaperCanonicalUniformCellIncrement B.sampleData
              (none, .minus)
              (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
                B R certificate deltaStar betaProt alpha qTilde) m *
            valuation p (B.sampleData.value m)) +
        ∑ m : B.sampleData.Sample,
          bankPaperCanonicalUniformCellIncrement B.sampleData
              (none, .plus)
              (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
                B R certificate deltaStar betaProt alpha qTilde) m *
            valuation p (B.sampleData.value m) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalTwoZeroHeadCellRebalance
      ring
    _ =
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalScaledActiveSeed T qTilde m *
            valuation p (B.sampleData.value m)) +
        (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde *
            (B.guardedCellProbability (none, .minus)).expect
              (fun m ↦ valuation p (m : Nat)) +
          bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde *
            (B.guardedCellProbability (none, .plus)).expect
              (fun m ↦ valuation p (m : Nat))) := by
      rw [
        sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
          B (none, .minus)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde) p,
        sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
          B (none, .plus)
            (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
              B R certificate deltaStar betaProt alpha qTilde) p]
      ring

/-! ## Exact label-one source decomposition -/





/-- Final exact decomposition.  Once the total mass has been synchronized,
the only large analytic comparison is the displayed scaled-active versus
guarded-broad moment; the nearest-integer contribution is already an
explicit two-cell term. -/
theorem
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_scaled_sub_guardedBase_add_nearestInteger
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (p : Nat)
    (hn : 1 <= B.sampleData.n) (hdeltaUpper : deltaStar <= 1)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1) :
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
        B K0 R certificate T deltaStar betaProt betaAct qTilde p =
      bankPaperCanonicalScaledActiveValuationMoment T qTilde p -
        bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
          B R certificate deltaStar betaAct p +
        bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p := by
  rw [
    roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_roundedActive_sub_guardedBase
      B K0 R certificate T deltaStar betaProt betaAct qTilde p
        hn hdeltaUpper hvalues,
    sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_valuation_eq_scaled_add_nearestInteger]
  ring

end BankPaperRealization

end

end Erdos390.WholePaper

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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureMixture -/
section


/-!
# Barycentric mixture algebra for the sharp smooth-source rate

The analytic marked-cell estimates compare every cell and the moving broad
pool to one common truncated prime-power profile.  This file performs the
remaining finite convex-mixture algebra exactly.

No cell-versus-broad rate is assumed.  The quantitative transfer theorem
takes two separate common-profile bounds, which are the outputs supplied by
the fixed-cell and moving-prefix analyses.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.FiniteProbability

noncomputable section

namespace BankPaperRealization

/-! ## Exact convex-mixture identities -/

/-- The scaled active valuation moment is the active mass times the
barycentric convex combination of the literal guarded-cell valuation
means. -/
theorem
    bankPaperCanonicalScaledActiveValuationMoment_eq_q_mul_cellMeans
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head}
    (T : BarycentricTarget D) (q : Real) (p : Nat) :
    bankPaperCanonicalScaledActiveValuationMoment T q p =
      q * ∑ c : Cell Head,
        T.cellProbability c *
          (uniformOnFinset (D.cellFinset c) (D.cell_nonempty c)).expect
            (fun m ↦ valuation p (m : Nat)) := by
  classical
  unfold bankPaperCanonicalScaledActiveValuationMoment
  unfold bankPaperCanonicalScaledActiveSeed
  rw [Fintype.sum_sigma]
  calc
    (∑ c : Cell Head, ∑ m : D.SampleAt c,
        q * T.baseline.baseWeight ⟨c, m⟩ *
          valuation p (D.value ⟨c, m⟩)) =
      ∑ c : Cell Head,
        q * T.cellProbability c *
          (uniformOnFinset (D.cellFinset c) (D.cell_nonempty c)).expect
            (fun m ↦ valuation p (m : Nat)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [FiniteProbability.uniformOnFinset_expect_eq]
      simp only [BaselineAllocation.baseWeight,
        StructuredSampleData.cellOf, StructuredSampleData.value,
        Fintype.card_coe]
      unfold BarycentricTarget.baseline
      rw [← Finset.mul_sum]
      ring
    _ = q * ∑ c : Cell Head,
        T.cellProbability c *
          (uniformOnFinset (D.cellFinset c) (D.cell_nonempty c)).expect
            (fun m ↦ valuation p (m : Nat)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _hc
      ring

/-- The constant guarded smooth-base moment is its literal mass times the
uniform valuation mean of the guarded broad pool. -/
theorem
    bankPaperCanonicalGuardedSmoothBaseValuationMoment_eq_mass_mul_poolMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaAct : Real) (p : Nat)
    (hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).Nonempty) :
    bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
        B R certificate deltaStar betaAct p =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
          deltaStar B.sampleData.W K betaAct *
        (uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hpool).expect
          (fun a ↦ valuation p (a : Nat)) := by
  unfold bankPaperCanonicalGuardedSmoothBaseValuationMoment
  unfold bankPaperCanonicalGuardedSmoothBaseMass
  rw [FiniteProbability.uniformOnFinset_expect_ambient_eq]
  unfold BridgeData.L Erdos390.Full.Scale.L
  have hcard :
      ((R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).card : Real) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hpool
  field_simp [hcard]

/-- After synchronizing `q` with the literal guarded smooth mass, the
unrounded active-versus-base moment is exactly mass times a difference of
probability means. -/
theorem
    bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_eq_mass_mul_meanDefect
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaAct q : Real) (p : Nat)
    (hq : q =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar B.sampleData.W K betaAct)
    (hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).Nonempty) :
    bankPaperCanonicalScaledActiveValuationMoment T q p -
        bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
          B R certificate deltaStar betaAct p =
      q *
        ((∑ cell : Cell (PaperHeadSimplex.Tag P),
            T.cellProbability cell *
              (B.guardedCellProbability cell).expect
                (fun m ↦ valuation p (m : Nat))) -
          (uniformOnFinset
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1) hpool).expect
                (fun a ↦ valuation p (a : Nat))) := by
  rw [
    bankPaperCanonicalScaledActiveValuationMoment_eq_q_mul_cellMeans,
    bankPaperCanonicalGuardedSmoothBaseValuationMoment_eq_mass_mul_poolMean
      B R certificate deltaStar betaAct p hpool,
    ← hq]
  unfold BridgeData.guardedCellProbability
  ring

/-! ## Common-profile quantitative transfer -/

/-- A convex combination and one broad-pool law inherit their difference
bound from separate estimates against the same common profile. -/
theorem
    abs_bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_le_of_commonProfile
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaAct q main Ccell Cpool : Real) (p : Nat)
    (hq : q =
      bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar B.sampleData.W K betaAct)
    (hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1).Nonempty)
    (_hp : 0 < p) (_hL : 0 < B.L)
    (_hCcell : 0 ≤ Ccell) (_hCpool : 0 ≤ Cpool)
    (hcell : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      |(B.guardedCellProbability cell).expect
          (fun m ↦ valuation p (m : Nat)) - main| ≤
        Ccell / ((p : Real) * B.L))
    (hpoolProfile :
      |(uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hpool).expect
          (fun a ↦ valuation p (a : Nat)) - main| ≤
        Cpool / ((p : Real) * B.L)) :
    |bankPaperCanonicalScaledActiveValuationMoment T q p -
        bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
          B R certificate deltaStar betaAct p| ≤
      |q| * ((Ccell + Cpool) / ((p : Real) * B.L)) := by
  let cellMean : Cell (PaperHeadSimplex.Tag P) → Real := fun cell ↦
    (B.guardedCellProbability cell).expect
      (fun m ↦ valuation p (m : Nat))
  let poolMean : Real :=
    (uniformOnFinset
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1) hpool).expect
      (fun a ↦ valuation p (a : Nat))
  have hmixIdentity :
      (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main =
        ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * (cellMean cell - main) := by
    calc
      (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main =
        (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) -
          (∑ cell : Cell (PaperHeadSimplex.Tag P),
            T.cellProbability cell) * main := by
          rw [T.sum_cellProbability, one_mul]
      _ = _ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro cell _hcell
        ring
  have hmix :
      |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main| ≤
        Ccell / ((p : Real) * B.L) := by
    rw [hmixIdentity]
    calc
      |∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * (cellMean cell - main)| ≤
        ∑ cell : Cell (PaperHeadSimplex.Tag P),
          |T.cellProbability cell * (cellMean cell - main)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * |cellMean cell - main| := by
        apply Finset.sum_congr rfl
        intro cell _hcell
        rw [abs_mul, abs_of_nonneg (T.cellProbability_pos cell).le]
      _ ≤ ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell *
            (Ccell / ((p : Real) * B.L)) := by
        apply Finset.sum_le_sum
        intro cell _hcell
        exact mul_le_mul_of_nonneg_left
          (by simpa only [cellMean] using hcell cell)
          (T.cellProbability_pos cell).le
      _ = Ccell / ((p : Real) * B.L) := by
        rw [← Finset.sum_mul, T.sum_cellProbability, one_mul]
  have hmeanPair :
      |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - poolMean| ≤
        (Ccell + Cpool) / ((p : Real) * B.L) := by
    calc
      |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - poolMean| ≤
        |(∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * cellMean cell) - main| +
          |poolMean - main| := by
            have htri := abs_add_le
              ((∑ cell : Cell (PaperHeadSimplex.Tag P),
                T.cellProbability cell * cellMean cell) - main)
              (main - poolMean)
            simpa only [sub_add_sub_cancel, abs_sub_comm] using htri
      _ ≤ Ccell / ((p : Real) * B.L) +
          Cpool / ((p : Real) * B.L) :=
        add_le_add hmix
          (by simpa only [poolMean] using hpoolProfile)
      _ = (Ccell + Cpool) / ((p : Real) * B.L) := by ring
  rw [
    bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_eq_mass_mul_meanDefect
      B R certificate T deltaStar betaAct q p hq hpool,
    abs_mul]
  exact mul_le_mul_of_nonneg_left hmeanPair (abs_nonneg q)

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureFinal -/
section


/-!
# Full sharp smooth-source valuation lift

This file combines the two separately proved common-profile estimates:

* every canonical guarded active cell; and
* the canonical guarded label-one broad pool.

The only remaining step is the exact barycentric algebra.  In particular,
the theorem below does not assume a cell-versus-pool valuation comparison.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PrimePowerCovariance
open Erdos390.Full.FiniteProbability

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-- The unrounded scaled active valuation moment and the constant guarded
smooth-base valuation moment differ by the sharp paper rate.  All analytic
inputs are discharged by the fixed-cell, moving-prefix, prime-power-tail,
guard-census, and barycentric theorems proved earlier in this closure chain.
-/
theorem
    exists_uniform_scaledActive_sub_guardedSmoothBase_valuationMoment_paperRate
    (Phead : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag Phead → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W K depth : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    {c : Real} (hc : 0 < c) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData (PaperHeadSimplex.Tag Phead) Band)
        (R : BankPaperRealization B.sampleData.n
          (upperEndpoint B.sampleData.n
            (upperTailLength c B.sampleData.n)))
        (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (T : BarycentricTarget B.sampleData)
        (deltaStar betaAct q : Real),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
            (rawCell Patterns I B.sampleData.n cell \
              (G B.sampleData.n).guards).Nonempty),
          B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Patterns I (G B.sampleData.n)
                hsep hremaining →
          q = bankPaperCanonicalGuardedSmoothBaseMass R certificate
              deltaStar B.sampleData.W K betaAct →
          ∀ _hpool :
            (R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1).Nonempty,
          ∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |bankPaperCanonicalScaledActiveValuationMoment T q p.1 -
                bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K)
                  B R certificate deltaStar betaAct p.1| ≤
              |q| * (Cval / ((p.1 : Real) * B.L)) := by
  obtain ⟨Ccell, hCcell, Ncell, hcellRate⟩ :=
    exists_uniform_bridge_guardedCell_valuation_mean_profiles_paperRate
      Patterns I Cprom Cbank G W hW hHeadLe
  obtain ⟨Cpool, hCpool, Npool, hpoolRate⟩ :=
    exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate
      W K depth hW hc
  let Cval : Real := Ccell + Cpool
  have hCval : 0 < Cval := by
    dsimp only [Cval]
    positivity
  refine ⟨Cval, hCval, max 2 (max Ncell Npool), ?_⟩
  intro Band _instBand _instBandDec B R certificate T
    deltaStar betaAct q hN hBW hsep hremaining hcanonical hq hpool p
  subst W
  have hn : 1 < B.sampleData.n := by omega
  have hNcell : Ncell ≤ B.sampleData.n := by omega
  have hNpool : Npool ≤ B.sampleData.n := by omega
  have hpBandW : p.1 ∈
      primeBand B.sampleData.n B.sampleData.W := p.2
  have hcell :=
    hcellRate B hNcell rfl hsep hremaining hcanonical p
  have hpoolProfile :=
    hpoolRate R certificate deltaStar hNpool hpBandW
      hpool
  let Kcut := Nat.log p.1 (yNat B.sampleData.n ^ 4)
  let mainSum := ∑ j ∈ positiveExponents Kcut,
    paperDivisibilityMain B.sampleData.n (p.1 ^ j)
  have hcell' :
      ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
        |(B.guardedCellProbability cell).expect
              (fun m ↦ valuation p.1 (m : Nat)) - mainSum| ≤
          Ccell / ((p.1 : Real) * B.L) := by
    intro cell
    simpa only [Kcut, mainSum] using hcell cell
  have hpool' :
      |(uniformOnFinset
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hpool).expect
          (fun a ↦ valuation p.1 (a : Nat)) - mainSum| ≤
        Cpool / ((p.1 : Real) * B.L) := by
    simpa only [Kcut, mainSum, BridgeData.L,
      Erdos390.Full.Scale.L] using hpoolProfile
  have hpPrime := prime_of_mem_primeBand p.2
  have hpPos : 0 < p.1 := hpPrime.pos
  have hL : 0 < B.L := by
    simpa only [BridgeData.L] using L_pos hn
  have hfinal :=
    abs_bankPaperCanonicalScaledActiveValuationMoment_sub_guardedSmoothBase_le_of_commonProfile
      B R certificate T deltaStar betaAct q mainSum Ccell Cpool p.1
      hq hpool hpPos hL hCcell.le hCpool.le hcell' hpool'
  simpa only [Cval] using hfinal

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpRoundedValuationRateConnector -/
section


/-!
# Rounded smooth-source to guarded valuation rate

The sharp common-profile closure controls the unrounded barycentric active
moment against the constant guarded label-one broad layer.  The exact
frozen-top decomposition has one additional term: the same nearest-integer
mass is inserted in each physical copy of the zero head cell.

This file bounds that literal correction directly.  Its cell mass is at most
`1 / 4`, by the universal half-unit nearest-integer error, and reciprocal
zero-cell valuation means then put it on the same
`secondOrderScale / (p * L)` scale.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.FiniteProbability

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## The synchronized guarded active mass -/

/-- The guarded label-one active mass has its pointwise paper-scale upper
bound without an additional analytic hypothesis.  Indeed, its support is
contained in the raw label-one smooth pool, which in turn lies in an
interval of cardinality at most `n`. -/
theorem
    abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) (betaAct : Real)
    (hn : 1 < n) :
    |bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar W K betaAct| ≤
      |betaAct| * secondOrderScale n := by
  have hL : 0 < L n := L_pos hn
  have hguardedSubset :
      R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1 ⊆
        bankPaperCanonicalRawSmoothBasePool W n h K := by
    simpa only [bankPaperCanonicalRawSmoothBasePool] using
      R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
        certificate deltaStar W K 1
  have hrawSubset :
      bankPaperCanonicalRawSmoothBasePool W n h K ⊆
        roughBroadLowerBlock n h K := by
    intro a ha
    change a ∈ roughCanonicalBroadCorrectionPool W n h K (yNat n) 1 at ha
    have haRow := mem_completeRoughRowFiber.mp ha
    exact (mem_roughHeadFree.mp haRow.1).1
  have hcardNat :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1).card ≤ n := by
    calc
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card ≤
          (bankPaperCanonicalRawSmoothBasePool W n h K).card :=
        Finset.card_le_card hguardedSubset
      _ ≤ (roughBroadLowerBlock n h K).card :=
        Finset.card_le_card hrawSubset
      _ ≤ n := by
        simp only [roughBroadLowerBlock, Nat.card_Ioc]
        omega
  have hcard :
      ((R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1).card : Real) ≤ (n : Real) := by
    exact_mod_cast hcardNat
  have hcardNonneg :
      (0 : Real) ≤
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card : Real) :=
    Nat.cast_nonneg _
  unfold bankPaperCanonicalGuardedSmoothBaseMass
  rw [abs_mul, abs_div, abs_of_pos hL, abs_of_nonneg hcardNonneg]
  rw [secondOrderScale]
  calc
    |betaAct| / L n *
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card : Real) ≤
        |betaAct| / L n * (n : Real) :=
      mul_le_mul_of_nonneg_left hcard
        (div_nonneg (abs_nonneg _) hL.le)
    _ = |betaAct| * ((n : Real) / L n) := by ring

/-! ## The literal nearest-integer correction -/





/-! ## Sharp rounded finite-rate connector -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPlacementValuationRateConnector -/
section


/-!
# Paper-rate valuation cost of the fresh post-height baseline

The rounded frozen-top source and the final post-height baseline are not the
same structured seed.  This file controls the valuation cost of replacing
the former by the latter.

There are three exact pieces.

* The structured placement moment is the tagged valuation moment of the new
  seed minus that of the old rounded seed.
* The old rounded moment is the synchronized scaled moment plus its literal
  nearest-integer correction.
* The new seed is the scaled post-height target at mass `q0-d`.

At a medium prime, both synchronized scaled moments are compared with the
same guarded smooth-base moment by the sharp common-profile theorem.  The
remaining mass change is bounded by `|q0-qTilde| + |d|`; nearest-integer
rounding gives the first term, and the Section 8 height ledger supplies the
second on the `secondOrderScale / L` scale.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperPrimePowerChamberError
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PaperRawTiltedValuationMeanRows

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Exact arbitrary-seed replacement moment -/

/-- On the complete smooth row, replacing an arbitrary two-zero-cell source
seed by an arbitrary fresh seed changes every valuation moment by the
difference of the two tagged seed moments. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment_arbitrarySeedReplacement_eq
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed newSeed : B.sampleData.Sample → Real)
    (outsideSelector : Nat → Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData →
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 →
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (p : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        newSeed p =
      (∑ m : B.sampleData.Sample,
          newSeed m * valuation p (B.sampleData.value m)) -
        ∑ m : B.sampleData.Sample,
          oldSeed m * valuation p (B.sampleData.value m) := by
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
    intro m
    exact hactiveSmooth
      (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
  unfold
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed outsideSelector)
              newSeed a -
          bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector a) *
          (a.factorization p : Real)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData newSeed a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) * valuation p a := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
          (K := K) B R certificate deltaStar betaProt oldSeed newSeed
            outsideSelector houtsideActive a]
      rfl
    _ =
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData newSeed a *
            valuation p a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a * valuation p a := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ =
        (∑ m : B.sampleData.Sample,
          newSeed m * valuation p (B.sampleData.value m)) -
          ∑ m : B.sampleData.Sample,
            oldSeed m * valuation p (B.sampleData.value m) := by
      rw [
        sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
          B.sampleData newSeed
            (R.roughCanonicalGuardedRow certificate deltaStar K 1)
            hvalues p,
        sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
          B.sampleData oldSeed
            (R.roughCanonicalGuardedRow certificate deltaStar K 1)
            hvalues p]

/-- For the literal rounded frozen-top source and the paper-faithful
post-height target, the placement moment is the post-height scaled moment
minus the synchronized scaled source moment and its nearest-integer term. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlacementValuationMoment_eq
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (p : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) p =
      bankPaperCanonicalScaledActiveValuationMoment
          (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
          (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) p -
        (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p +
          bankPaperCanonicalTopFrozenNearestIntegerValuationMoment (K := K)
            B R certificate deltaStar betaProt alpha qTilde p) := by
  let oldSeed :=
    bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
      B R certificate Tsource deltaStar betaProt alpha qTilde
  let newSeed :=
    bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H
  have hcompat :
      BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
        (K := K) B R certificate Tsource deltaStar betaProt
          alpha beta qTilde :=
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport
      (K := K) B R certificate Tsource deltaStar betaProt
        alpha beta qTilde hactiveSmooth hactiveBroad
  have hexact :=
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment_arbitrarySeedReplacement_eq
      (K := K) B R certificate deltaStar betaProt oldSeed newSeed
        (bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
          B R certificate deltaStar alpha beta oldSeed)
        hcompat hactiveSmooth p
  have hold :=
    sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_valuation_eq_scaled_add_nearestInteger
      (K := K) B R certificate Tsource deltaStar betaProt alpha qTilde p
  calc
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) p =
      (∑ m : B.sampleData.Sample,
          newSeed m * valuation p (B.sampleData.value m)) -
        ∑ m : B.sampleData.Sample,
          oldSeed m * valuation p (B.sampleData.value m) := by
      simpa only [
        oldSeed, newSeed,
        bankPaperCanonicalTopFrozenRoundedSourceSelector,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop] using hexact
    _ =
      bankPaperCanonicalScaledActiveValuationMoment
          (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
          (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) p -
        (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p +
          bankPaperCanonicalTopFrozenNearestIntegerValuationMoment (K := K)
            B R certificate deltaStar betaProt alpha qTilde p) := by
      rw [show
        (∑ m : B.sampleData.Sample,
            newSeed m * valuation p (B.sampleData.value m)) =
          bankPaperCanonicalScaledActiveValuationMoment
            (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
            (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) p by
          rfl]
      simpa only [oldSeed] using congrArg
        (fun x : Real =>
          bankPaperCanonicalScaledActiveValuationMoment
              (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
              (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) p -
            x)
        hold

/-! ## A finite mass-shift estimate -/

/-- Changing only the scalar mass of one barycentric target costs its mass
change times the convexly averaged cell valuation mean. -/
theorem
    abs_bankPaperCanonicalScaledActiveValuationMoment_sub_of_massChange
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (T : BarycentricTarget B.sampleData)
    (qNew qOld Aval Cmass : Real) (p : Nat)
    (hp : p.Prime)
    (hmean : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      (B.guardedCellProbability cell).expect
          (fun m ↦ valuation p (m : Nat)) ≤ Aval / (p : Real))
    (hmass :
      |qNew - qOld| ≤
        Cmass * (secondOrderScale B.sampleData.n / B.L)) :
    |bankPaperCanonicalScaledActiveValuationMoment T qNew p -
        bankPaperCanonicalScaledActiveValuationMoment T qOld p| ≤
      (Cmass * Aval) *
        (secondOrderScale B.sampleData.n / ((p : Real) * B.L)) := by
  let mean : Real :=
    ∑ cell : Cell (PaperHeadSimplex.Tag P),
      T.cellProbability cell *
        (B.guardedCellProbability cell).expect
          (fun m ↦ valuation p (m : Nat))
  have hpR : 0 < (p : Real) := by exact_mod_cast hp.pos
  have hL : 0 < B.L := B.L_pos
  have hmassRhs0 :
      0 ≤ Cmass * (secondOrderScale B.sampleData.n / B.L) :=
    (abs_nonneg (qNew - qOld)).trans hmass
  have hmean0 : 0 ≤ mean := by
    dsimp only [mean]
    exact Finset.sum_nonneg fun cell _hcell =>
      mul_nonneg (T.cellProbability_pos cell).le
        ((B.guardedCellProbability cell).expect_nonneg _
          (fun m ↦ valuation_nonneg p (m : Nat)))
  have hmeanUpper : mean ≤ Aval / (p : Real) := by
    dsimp only [mean]
    calc
      (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell *
            (B.guardedCellProbability cell).expect
              (fun m ↦ valuation p (m : Nat))) ≤
        ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * (Aval / (p : Real)) := by
            apply Finset.sum_le_sum
            intro cell _hcell
            exact mul_le_mul_of_nonneg_left
              (hmean cell) (T.cellProbability_pos cell).le
      _ = Aval / (p : Real) := by
        rw [← Finset.sum_mul, T.sum_cellProbability, one_mul]
  rw [
    bankPaperCanonicalScaledActiveValuationMoment_eq_q_mul_cellMeans,
    bankPaperCanonicalScaledActiveValuationMoment_eq_q_mul_cellMeans]
  change |qNew * mean - qOld * mean| ≤ _
  rw [← sub_mul, abs_mul, abs_of_nonneg hmean0]
  calc
    |qNew - qOld| * mean ≤
        (Cmass * (secondOrderScale B.sampleData.n / B.L)) *
          (Aval / (p : Real)) := by
      exact mul_le_mul hmass hmeanUpper hmean0
        hmassRhs0
    _ = (Cmass * Aval) *
        (secondOrderScale B.sampleData.n / ((p : Real) * B.L)) := by
      field_simp [hpR.ne', hL.ne']

/-! ## Uniform sharp post-height placement rate -/

/-- The arbitrary post-height seed replacement has the medium-prime paper
rate.  The only height input is the literal pointwise consequence of the
Section 8 ledger, `|d| = O(secondOrderScale / L)`; all valuation estimates
are discharged here by the existing canonical common-profile chain.

The constant is uniform in the bridge, bank, certificate, source target,
post-height target data, and medium prime. -/
theorem
    exists_uniform_sectionNinePostHeightPlacementValuationMoment_paperRate
    (Phead : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag Phead → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W K0 depth : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    {c : Real} (hc : 0 < c)
    (betaAct Azero Cd : Real)
    (hAzero : 0 ≤ Azero) (hCd : 0 ≤ Cd) :
    ∃ Cplacement : Real, 0 < Cplacement ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData (PaperHeadSimplex.Tag Phead) Band)
        (R : BankPaperRealization B.sampleData.n
          (upperEndpoint B.sampleData.n
            (upperTailLength c B.sampleData.n)))
        (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (Tsource : BarycentricTarget B.sampleData)
        (hlo : ∀ sigma, B.sampleData.lo sigma =
          physicalBound (I.lower sigma) B.sampleData.n)
        (hhi : ∀ sigma, B.sampleData.hi sigma =
          physicalBound (I.upper sigma) B.sampleData.n)
        {q0 A0 : Real} {d : Int} {exponent : Nat}
        {activeHeadTarget : {p : Nat // p ∈ Phead} → Real}
        (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
          B I q0 A0 d exponent activeHeadTarget)
        (deltaStar betaProt qTilde : Real),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
            (rawCell Patterns I B.sampleData.n cell \
              (G B.sampleData.n).guards).Nonempty),
          B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Patterns I (G B.sampleData.n)
                hsep hremaining →
          qTilde = bankPaperCanonicalGuardedSmoothBaseMass R certificate
              deltaStar B.sampleData.W (K0 + 1) betaAct →
          deltaStar ≤ 1 →
          (∀ m : B.sampleData.Sample,
            B.sampleData.value m ∈
              R.roughCanonicalGuardedRow certificate deltaStar
                (K0 + 1) 1) →
          (∀ m : B.sampleData.Sample,
            B.sampleData.value m ∈
              roughBroadLowerBlock B.sampleData.n
                (upperTailLength c B.sampleData.n) (K0 + 1)) →
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W (K0 + 1) 1).Nonempty →
          q0 =
            bankPaperCanonicalTopFrozenRoundedActiveMass (K := K0 + 1)
              B R certificate deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde →
          |(d : Real)| ≤
            Cd * (secondOrderScale B.sampleData.n / B.L) →
          ∀ p : BandPrime B.sampleData.n B.sampleData.W,
            (∀ sigma : PhysicalSign,
              (B.guardedCellProbability (none, sigma)).expect
                  (fun m ↦ valuation p.1 (m : Nat)) ≤
                Azero / (p.1 : Real)) →
            |bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaProt
                (bankPaperCanonicalTopFrozenRoundedSourceSelector
                  (K := K0 + 1) B R certificate Tsource deltaStar betaProt
                    (bankPaperCanonicalPostHfitBalancedAlpha
                      B c K0 betaProt betaAct)
                    (betaProt + betaAct) qTilde)
                (bankPaperCanonicalSectionNinePostHeightActiveSeed
                  B I hlo hhi H) p.1| ≤
              Cplacement *
                (secondOrderScale B.sampleData.n /
                  ((p.1 : Real) * B.L)) := by
  obtain ⟨Csource, hCsource, Nsource, hsource⟩ :=
    exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate
      Phead Patterns I Cprom Cbank G W K0 depth hW hHeadLe hc
        betaAct Azero hAzero
  obtain ⟨Csharp, hCsharp, Nsharp, hsharp⟩ :=
    exists_uniform_scaledActive_sub_guardedSmoothBase_valuationMoment_paperRate
      Phead Patterns I Cprom Cbank G W (K0 + 1) depth hW hHeadLe hc
  obtain ⟨Ccell, hCcell, Ncell, hcellProfile⟩ :=
    exists_uniform_bridge_guardedCell_valuation_mean_profiles_paperRate
      Patterns I Cprom Cbank G W hW hHeadLe
  let Amain : Real := 6 / rho DickmanBasic.U
  let Aval : Real := Amain + Ccell
  let Cmass : Real := Cd + 1
  let Cplacement : Real :=
    Csource + |betaAct| * Csharp + Cmass * Aval + 1
  have hAmain : 0 < Amain := by
    dsimp only [Amain]
    exact div_pos (by norm_num) DickmanBasic.rho_U_pos
  have hAval : 0 < Aval := by
    dsimp only [Aval]
    exact add_pos hAmain hCcell
  have hCmass : 0 ≤ Cmass := by
    dsimp only [Cmass]
    linarith
  have hbetaTerm : 0 ≤ |betaAct| * Csharp :=
    mul_nonneg (abs_nonneg betaAct) hCsharp.le
  have hmassTerm : 0 ≤ Cmass * Aval :=
    mul_nonneg hCmass hAval.le
  have hCplacement : 0 < Cplacement := by
    dsimp only [Cplacement]
    nlinarith
  have hscaleEvent : ∀ᶠ n : Nat in atTop,
      1 ≤ secondOrderScale n / L n :=
    secondOrderScale_div_L_tendsto_atTop.eventually
      (eventually_ge_atTop 1)
  have hLtendsto : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogEvent : ∀ᶠ n : Nat in atTop, 1 ≤ L n :=
    hLtendsto.eventually (eventually_ge_atTop 1)
  obtain ⟨Nscale, hNscale⟩ := Filter.eventually_atTop.mp hscaleEvent
  obtain ⟨Nlog, hNlog⟩ := Filter.eventually_atTop.mp hlogEvent
  refine
    ⟨Cplacement, hCplacement,
      max 2 (max Nsource (max Nsharp (max Ncell (max Nscale Nlog)))),
      ?_⟩
  intro Band _instBand _instBandDec B R certificate Tsource hlo hhi
    q0 A0 d exponent activeHeadTarget H deltaStar betaProt qTilde
    hN hBW hsep hremaining hcanonical hmassSync hdeltaUpper
    hvalues hactiveBroad hpool hq0 hd p hzeroMean
  have hn : 1 < B.sampleData.n := by omega
  have hNsource : Nsource ≤ B.sampleData.n := by omega
  have hNsharp : Nsharp ≤ B.sampleData.n := by omega
  have hNcell : Ncell ≤ B.sampleData.n := by omega
  have hNscaleBound : Nscale ≤ B.sampleData.n := by omega
  have hNlogBound : Nlog ≤ B.sampleData.n := by omega
  have hp := prime_of_mem_primeBand p.2
  have hpR : 0 < (p.1 : Real) := by exact_mod_cast hp.pos
  have hL : 0 < B.L := B.L_pos
  have hLone : 1 ≤ B.L := by
    simpa only [BridgeData.L] using hNlog B.sampleData.n hNlogBound
  have hscaleHeightOne :
      1 ≤ secondOrderScale B.sampleData.n / B.L := by
    simpa only [BridgeData.L] using
      hNscale B.sampleData.n hNscaleBound
  let scale : Real :=
    secondOrderScale B.sampleData.n / ((p.1 : Real) * B.L)
  have hscale0 : 0 ≤ scale := by
    dsimp only [scale]
    exact div_nonneg (secondOrderScale_pos (by omega)).le
      (mul_nonneg hpR.le hL.le)
  let Tpost :=
    bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H
  let qn :=
    bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  have hqBound :
      |qTilde| ≤ |betaAct| * secondOrderScale B.sampleData.n := by
    rw [hmassSync]
    exact
      abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
        R certificate deltaStar B.sampleData.W (K0 + 1) betaAct hn
  have hprincipalRaw :=
    hsharp B R certificate Tpost deltaStar betaAct qTilde
      hNsharp hBW hsep hremaining hcanonical hmassSync hpool p
  have hprincipal :
      |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1| ≤
        (|betaAct| * Csharp) * scale := by
    calc
      |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1| ≤
        |qTilde| * (Csharp / ((p.1 : Real) * B.L)) :=
          hprincipalRaw
      _ ≤ (|betaAct| * secondOrderScale B.sampleData.n) *
          (Csharp / ((p.1 : Real) * B.L)) := by
        exact mul_le_mul_of_nonneg_right hqBound
          (div_nonneg hCsharp.le (mul_nonneg hpR.le hL.le))
      _ = (|betaAct| * Csharp) * scale := by
        dsimp only [scale]
        ring
  have hsourceRaw :=
    hsource B R certificate Tsource deltaStar betaProt qTilde
      hNsource hBW hsep hremaining hcanonical hmassSync hdeltaUpper
        hvalues hpool p hzeroMean
  have hsourceBound :
      |bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1 +
        bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p.1| ≤
        Csource * scale := by
    unfold
      RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
      at hsourceRaw
    rw [
      roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_scaled_sub_guardedBase_add_nearestInteger
        B K0 R certificate Tsource deltaStar betaProt betaAct qTilde p.1
          (by omega) hdeltaUpper hvalues] at hsourceRaw
    simpa only [scale] using hsourceRaw
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
  have hcellMean :
      ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
        (B.guardedCellProbability cell).expect
            (fun m ↦ valuation p.1 (m : Nat)) ≤
          Aval / (p.1 : Real) := by
    intro cell
    let mean :=
      (B.guardedCellProbability cell).expect
        (fun m ↦ valuation p.1 (m : Nat))
    have hprofile :
        |mean - mainSum| ≤ Ccell / ((p.1 : Real) * B.L) := by
      simpa only [mean, Kcut, mainSum] using hcellRaw cell
    have herror :
        Ccell / ((p.1 : Real) * B.L) ≤
          Ccell / (p.1 : Real) := by
      apply div_le_div_of_nonneg_left hCcell.le hpR
      calc
        (p.1 : Real) = (p.1 : Real) * 1 := by ring
        _ ≤ (p.1 : Real) * B.L :=
          mul_le_mul_of_nonneg_left hLone hpR.le
    have hmeanLe : mean ≤ mainSum +
        Ccell / ((p.1 : Real) * B.L) := by
      have hself : mean - mainSum ≤ |mean - mainSum| :=
        le_abs_self _
      linarith
    calc
      mean ≤ mainSum + Ccell / ((p.1 : Real) * B.L) := hmeanLe
      _ ≤ Amain / (p.1 : Real) + Ccell / (p.1 : Real) :=
        add_le_add hmainUpper herror
      _ = Aval / (p.1 : Real) := by
        dsimp only [Aval]
        ring
  have hround :
      |q0 - qTilde| ≤ (1 : Real) / 2 := by
    rw [hq0]
    unfold bankPaperCanonicalTopFrozenRoundedActiveMass
    exact bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le _ _
  have hmassChange :
      |qn - qTilde| ≤
        Cmass * (secondOrderScale B.sampleData.n / B.L) := by
    have htriangle :
        |qn - qTilde| ≤ |q0 - qTilde| + |(d : Real)| := by
      calc
        |qn - qTilde| = |(q0 - qTilde) - (d : Real)| := by
          congr 1
          dsimp only [qn]
          unfold bankPaperCanonicalSectionNinePostHeightActiveMass
          ring
        _ ≤ |q0 - qTilde| + |(d : Real)| :=
          abs_sub _ _
    calc
      |qn - qTilde| ≤ |q0 - qTilde| + |(d : Real)| :=
        htriangle
      _ ≤ (1 : Real) / 2 +
          Cd * (secondOrderScale B.sampleData.n / B.L) :=
        add_le_add hround hd
      _ ≤ Cmass * (secondOrderScale B.sampleData.n / B.L) := by
        dsimp only [Cmass]
        nlinarith
  have hmassMoment :=
    abs_bankPaperCanonicalScaledActiveValuationMoment_sub_of_massChange
      B Tpost qn qTilde Aval Cmass p.1 hp hcellMean hmassChange
  have hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1 := by
    intro a ha
    obtain ⟨m, rfl⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp ha
    exact hvalues m
  have hexact :=
    bankPaperCanonicalSectionNinePostHeightPlacementValuationMoment_eq
      (K := K0 + 1) B R certificate Tsource I hlo hhi H
        deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) qTilde hactiveSmooth hactiveBroad p.1
  rw [hexact]
  have htriangle :
      |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
          (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
            bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde p.1)| ≤
        |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
            bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1| +
          |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
            bankPaperCanonicalGuardedSmoothBaseValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaAct p.1| +
          |bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 -
              bankPaperCanonicalGuardedSmoothBaseValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaAct p.1 +
            bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde p.1| := by
    have htri1 := abs_add_le
      (bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
        bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1)
      (bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
        (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
          bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              qTilde p.1))
    have htri2 :
        |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
            (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
              bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaProt
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  qTilde p.1)| ≤
          |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
            bankPaperCanonicalGuardedSmoothBaseValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaAct p.1| +
          |bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 -
              bankPaperCanonicalGuardedSmoothBaseValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaAct p.1 +
            bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde p.1| := by
      have h := abs_add_le
        (bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaAct p.1)
        (bankPaperCanonicalGuardedSmoothBaseValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaAct p.1 -
          (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
            bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde p.1))
      calc
        _ =
            |(bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
                bankPaperCanonicalGuardedSmoothBaseValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaAct p.1) +
              (bankPaperCanonicalGuardedSmoothBaseValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaAct p.1 -
                (bankPaperCanonicalScaledActiveValuationMoment
                    Tsource qTilde p.1 +
                  bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                    (K := K0 + 1) B R certificate deltaStar betaProt
                      (bankPaperCanonicalPostHfitBalancedAlpha
                        B c K0 betaProt betaAct)
                      qTilde p.1))| := by
              congr 1
              ring
        _ ≤
            |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
              bankPaperCanonicalGuardedSmoothBaseValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaAct p.1| +
            |bankPaperCanonicalGuardedSmoothBaseValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaAct p.1 -
              (bankPaperCanonicalScaledActiveValuationMoment
                  Tsource qTilde p.1 +
                bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaProt
                    (bankPaperCanonicalPostHfitBalancedAlpha
                      B c K0 betaProt betaAct)
                    qTilde p.1)| := h
        _ = _ := by
          congr 1
          rw [show
            bankPaperCanonicalGuardedSmoothBaseValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaAct p.1 -
                (bankPaperCanonicalScaledActiveValuationMoment
                    Tsource qTilde p.1 +
                  bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                    (K := K0 + 1) B R certificate deltaStar betaProt
                      (bankPaperCanonicalPostHfitBalancedAlpha
                        B c K0 betaProt betaAct)
                      qTilde p.1) =
              -(bankPaperCanonicalScaledActiveValuationMoment
                    Tsource qTilde p.1 -
                  bankPaperCanonicalGuardedSmoothBaseValuationMoment
                    (K := K0 + 1) B R certificate deltaStar betaAct p.1 +
                bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaProt
                    (bankPaperCanonicalPostHfitBalancedAlpha
                      B c K0 betaProt betaAct)
                    qTilde p.1) by ring,
            abs_neg]
    calc
      _ ≤
          |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
            bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1| +
          |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
            (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
              bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaProt
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  qTilde p.1)| := by
            simpa only [sub_add_sub_cancel] using htri1
      _ ≤
          |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
            bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1| +
          (|bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
              bankPaperCanonicalGuardedSmoothBaseValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaAct p.1| +
            |bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 -
                bankPaperCanonicalGuardedSmoothBaseValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaAct p.1 +
              bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaProt
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  qTilde p.1|) := by
            exact add_le_add (le_refl _) htri2
      _ = _ := by ring
  calc
    |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
        (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
          bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              qTilde p.1)| ≤
      |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
          bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1| +
        |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaAct p.1| +
        |bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 -
            bankPaperCanonicalGuardedSmoothBaseValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaAct p.1 +
          bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              qTilde p.1| := htriangle
    _ ≤ (Cmass * Aval) * scale +
        (|betaAct| * Csharp) * scale +
        Csource * scale :=
      add_le_add (add_le_add hmassMoment hprincipal) hsourceBound
    _ = (Csource + |betaAct| * Csharp + Cmass * Aval) * scale := by
      ring
    _ ≤ Cplacement * scale := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp only [Cplacement]; linarith) hscale0
    _ = Cplacement *
        (secondOrderScale B.sampleData.n / ((p.1 : Real) * B.L)) := by
      rfl

end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal007_012.{u_1} := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_uniform_sectionNinePostHeightPlacementValuationMoment_paperRate
