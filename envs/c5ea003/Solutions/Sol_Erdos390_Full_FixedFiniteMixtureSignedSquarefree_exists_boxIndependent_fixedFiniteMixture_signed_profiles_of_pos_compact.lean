-- Prove2me | solution 1 for Erdos390.Full.FixedFiniteMixtureSignedSquarefree.exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:11:34.661255+00:00
-- url     : https://prove2.me/submissions/0fdea24a-0874-4bd7-931b-436e1ae603ab

import Definitions.Def_erdos390_remaining_analytic_propositions_001
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004
import Theorems.Thm_Erdos390_Full_FullTiltPairHarmonicRate_exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate_compact
import Theorems.Thm_Erdos390_Full_LocalFugacityBounds_coefficientTail_le
import Theorems.Thm_Erdos390_Full_PaperPrimePowerRemainderRate_tendsto_primePowerChamberRemainder_zero_and_rate


section
theorem Erdos390.Full.FullTiltPairHarmonicRate.exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate : Erdos390.RemainingAnalyticGoal001_004 := @Erdos390.Full.FullTiltPairHarmonicRate.exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate_compact
end
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









theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

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











theorem headDensity_pos (P : Pattern) : 0 < headDensity P := by
  have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
  have hmod : (0 : ℝ) < (P.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.modulus_ne_zero
  have htot : (0 : ℝ) < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero P.modulus_ne_zero)
  exact mul_pos (one_div_pos.mpr hfactor) (div_pos htot hmod)



/-! ## The common paper-scale main term -/





theorem paperCellDensity_pos (P : Pattern) {A B : ℝ} (hAB : A < B) :
    0 < paperCellDensity P A B := by
  exact mul_pos (mul_pos (headDensity_pos P) (sub_pos.mpr hAB)) rho_U_pos











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































theorem coefficientTail_nonneg (p A r : ℕ) (eta L : ℝ) :
    0 ≤ coefficientTail p A r eta L := by
  unfold coefficientTail
  positivity











end

end Erdos390.Full.LocalFugacityBounds

end

/- Source module: Erdos390.Full.ValuationCutoff -/
section


/-!
# The actual logarithmic valuation cutoff

The local fugacity expansion must be truncated at
`floor(log M / log p)`, not at the much larger physical endpoint `M`.
This module identifies Mathlib's `Nat.log p M` as a valid common cutoff for
all positive integers `m ≤ M`, proves the exact restored factor at that
cutoff, and compares it with the real logarithmic ratio used in the paper.
-/

namespace Erdos390.Full.ValuationCutoff

open ArithmeticModel LocalFugacityRestoration

noncomputable section









/-- The natural logarithmic cutoff is no larger than the corresponding real
logarithmic ratio. -/
theorem cast_valuationCutoff_le_log_ratio
    {p M : ℕ} (hp : 1 < p) (hM : 0 < M) :
    (valuationCutoff p M : ℝ) ≤
      Real.log (M : ℝ) / Real.log (p : ℝ) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hpowNat : p ^ valuationCutoff p M ≤ M := by
    exact Nat.pow_log_le_self p hM.ne'
  have hpowPos : (0 : ℝ) < ((p ^ valuationCutoff p M : ℕ) : ℝ) := by
    positivity
  have hpowCast : ((p ^ valuationCutoff p M : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log hpowPos hpowCast
  norm_num only [Nat.cast_pow] at hlog
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ hlogp).2
  simpa [mul_comm] using hlog



end

end Erdos390.Full.ValuationCutoff

end

/- Source module: Erdos390.Full.PaperValuationCutoff -/
section


/-!
# Paper-scale bounds for the logarithmic valuation cutoff

At the physical scale `m ≤ C n` and for `W < p ≤ n^(2/9)`, the exact local
cutoff is `O(L / log W)`.  This turns every restored coefficient tail into
`L⁻¹ p^{-r}` with an exponential constant depending on the already fixed
box and cutoff, while leaving the leading prime-power constant independent
of that box.
-/

open Filter Topology

namespace Erdos390.Full.PaperValuationCutoff

open ArithmeticModel Scale
open ValuationCutoff LocalFugacityBounds

noncomputable section

/-- The logarithmic valuation-cutoff estimate only needs a positive physical
upper endpoint.  The older `1 ≤ C` formulation below is retained as a
compatibility wrapper, but that normalization is not part of the paper's
cell hypotheses. -/
theorem eventually_valuationCutoff_div_L_le_of_pos
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        2 / Real.log (W : ℝ) := by
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [hCevent, hInvCevent, Filter.eventually_gt_atTop 1]
    with n hCn hInvCn hn
  intro p hpBand
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hpPrime : p.Prime := prime_of_mem_primeBand hpBand
  have hpW : W < p := cutoff_lt_of_mem_primeBand hpBand
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hlogWp : Real.log (W : ℝ) ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hW.le)
    exact_mod_cast hpW.le
  have hOneMul : (1 : ℝ) ≤ C * (n : ℝ) := by
    have h := (div_le_iff₀ hC).mp hInvCn
    simpa [mul_comm] using h
  have hphysOne : 1 ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    exact_mod_cast hOneMul
  have hM : 0 < physicalBound C n := lt_of_lt_of_le Nat.zero_lt_one hphysOne
  have hphysCast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogPhys : Real.log (physicalBound C n : ℝ) ≤ 2 * L n := by
    have hleSq : (physicalBound C n : ℝ) ≤ (n : ℝ) ^ 2 :=
      hphysCast.trans hCnSq
    have hlog := Real.log_le_log (by exact_mod_cast hM) hleSq
    rw [Real.log_pow] at hlog
    simpa [L] using hlog
  have hlogPhys0 : 0 ≤ Real.log (physicalBound C n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hphysOne)
  have hcut := cast_valuationCutoff_le_log_ratio hpPrime.one_lt hM
  have hratio :
      Real.log (physicalBound C n : ℝ) / Real.log (p : ℝ) ≤
        (2 * L n) / Real.log (W : ℝ) := by
    calc
      _ ≤ Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ) :=
        div_le_div_of_nonneg_left hlogPhys0 hlogW hlogWp
      _ ≤ (2 * L n) / Real.log (W : ℝ) :=
        div_le_div_of_nonneg_right hlogPhys hlogW.le
  calc
    (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        (Real.log (physicalBound C n : ℝ) / Real.log (p : ℝ)) / L n :=
      div_le_div_of_nonneg_right hcut hL.le
    _ ≤ ((2 * L n) / Real.log (W : ℝ)) / L n :=
      div_le_div_of_nonneg_right hratio hL.le
    _ = 2 / Real.log (W : ℝ) := by
      field_simp [hL.ne', hlogW.ne']







/-- Positive-endpoint version of `eventually_coefficientTail_le`. -/
theorem eventually_coefficientTail_le_of_pos
    (B C : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ eta : ℝ,
      |eta| ≤ B → ∀ r : ℕ,
      coefficientTail p (valuationCutoff p (physicalBound C n)) r eta (L n) ≤
        ((2 * B / L n) * Real.exp (2 * B / Real.log (W : ℝ))) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hBLEvent : ∀ᶠ n : ℕ in atTop, B ≤ L n :=
    hLTop.eventually (eventually_ge_atTop B)
  filter_upwards [eventually_valuationCutoff_div_L_le_of_pos C W hC hW,
    hBLEvent, Filter.eventually_gt_atTop 1] with n hcut hBL hn
  intro p hpBand eta heta r
  have hL : 0 < L n := L_pos hn
  have hp2 : 2 ≤ p := (prime_of_mem_primeBand hpBand).two_le
  have hcut' := hcut p hpBand
  have hexponent :
      B * (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        2 * B / Real.log (W : ℝ) := by
    calc
      B * (valuationCutoff p (physicalBound C n) : ℝ) / L n =
          B * ((valuationCutoff p (physicalBound C n) : ℝ) / L n) := by
        ring
      _ ≤ B * (2 / Real.log (W : ℝ)) :=
        mul_le_mul_of_nonneg_left hcut' hB
      _ = 2 * B / Real.log (W : ℝ) := by ring
  have hraw := coefficientTail_le (A := valuationCutoff p (physicalBound C n))
    hp2 hB hL hBL heta (r := r)
  have hcoef : 0 ≤ 2 * B / L n := by positivity
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hcoef)
    (by positivity))





end

end Erdos390.Full.PaperValuationCutoff

end

/- Source module: Erdos390.Full.OmittedTiltPairChamber -/
section


/-!
# The actual omitted-tilt two-prime four-mark chamber

This file specializes the uniform marked-divisibility theorem to the literal
moduli `p^a q^b` occurring in the two-local restoration of Lemma 7.5.  All
side conditions are discharged from membership of `p,q` in the paper prime
band, the four-mark inequality `a+b <= 4`, and coprimality with the fixed
head.  In particular, the theorem below is about the genuine structured
cell and the genuine omitted valuation score, not an abstract probability
law or a conditional analytic contract.
-/

open Filter Topology

namespace Erdos390.Full.OmittedTiltPairChamber

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability ValuationScoreDomination
open PaperScaleMarkedCell OmittedTiltMarkedProbability
open TwoLocalRestoration

noncomputable section



theorem pairPower_pos {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) :
    0 < pairPower p q a b := by
  unfold pairPower
  exact Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.pow_pos hq.pos)











end

end Erdos390.Full.OmittedTiltPairChamber

end

/- Source module: Erdos390.Full.TwoLocalRestorationBound -/
section


/-!
# Quantitative error of the exact two-local restoration

This file bounds every nonconstant term in the exact `N_{r,s}` numerator
using the arbitrary-modulus reciprocal fallback.  The result retains the
paper's weighted coefficient tails in both local coordinates; in particular,
it does not replace them by the cardinality of the exponent cutoff.
-/

open scoped BigOperators

namespace Erdos390.Full.TwoLocalRestorationBound

open ArithmeticModel FiniteProbability LocalFugacity LocalFugacityBounds
open OmittedTiltPairChamber

noncomputable section

variable {Omega : Type*} [Fintype Omega]





theorem pairRestorationError_nonneg (p q Ap Aq r s : ℕ)
    (etaP etaQ L G : ℝ) (hG : 0 ≤ G) :
    0 ≤ pairRestorationError p q Ap Aq r s etaP etaQ L G := by
  have hpTail := coefficientTail_nonneg p Ap r etaP L
  have hqTail := coefficientTail_nonneg q Aq s etaQ L
  have hpInv : 0 ≤ 1 / (p : ℝ) ^ r := by positivity
  have hqInv : 0 ≤ 1 / (q : ℝ) ^ s := by positivity
  unfold pairRestorationError
  exact add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hG hpTail) hqInv)
      (mul_nonneg (mul_nonneg hG hpInv) hqTail))
    (mul_nonneg (mul_nonneg hG hpTail) hqTail)

















end

end Erdos390.Full.TwoLocalRestorationBound

end

/- Source module: Erdos390.Full.PaperTwoLocalRestorationBound -/
section


/-!
# Paper-scale stability of the two-local normalizer

The exact restoration quotient is useful only after its denominator is shown
uniformly away from zero.  This file performs that quantifier step at the
actual paper scale.  The fallback density-ratio constant is first bounded by
a fixed `B,W,c` ceiling, and the two coefficient tails then tend uniformly to
zero over the moving prime band.
-/

open Filter Topology

namespace Erdos390.Full.PaperTwoLocalRestorationBound

open ArithmeticModel Scale LocalFugacityBounds PaperValuationCutoff
open ValuationCutoff
open TwoLocalRestorationBound

noncomputable section





theorem paperPairFallbackConstant_nonneg (B C c : ℝ) (W n : ℕ)
    (hc : 0 ≤ c) :
    0 ≤ paperPairFallbackConstant B C c W n := by
  unfold paperPairFallbackConstant
  positivity

theorem paperPairFallbackCeiling_pos (B c : ℝ) (W : ℕ) (hc : 0 < c) :
    0 < paperPairFallbackCeiling B c W := by
  unfold paperPairFallbackCeiling
  positivity

/-- The moving physical endpoint contributes no `n`-dependent loss to the
fallback density-ratio constant. -/
theorem eventually_paperPairFallbackConstant_le
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      paperPairFallbackConstant B C c W n ≤
        paperPairFallbackCeiling B c W := by
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [hCevent, hInvCevent, Filter.eventually_gt_atTop 1]
    with n hCn hInvCn hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hphysLower : 1 ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
      have := (div_le_iff₀ hC).mp hInvCn
      simpa [mul_comm] using this
    exact_mod_cast hOne
  have hphysPos : 0 < physicalBound C n :=
    lt_of_lt_of_le Nat.zero_lt_one hphysLower
  have hphysCast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogPhys : Real.log (physicalBound C n : ℝ) ≤ 2 * L n := by
    have hleSq : (physicalBound C n : ℝ) ≤ (n : ℝ) ^ 2 :=
      hphysCast.trans hCnSq
    have hlog := Real.log_le_log (by exact_mod_cast hphysPos) hleSq
    rw [Real.log_pow] at hlog
    simpa [L] using hlog
  have hK : 2 * ((B / L n) *
      (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) ≤
      4 * B / Real.log (W : ℝ) := by
    calc
      _ ≤ 2 * ((B / L n) *
          ((2 * L n) / Real.log (W : ℝ))) := by gcongr
      _ = 4 * B / Real.log (W : ℝ) := by
        field_simp [hL.ne', hlogW.ne']
        ring
  unfold paperPairFallbackConstant paperPairFallbackCeiling
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hK) hc.le



end

end Erdos390.Full.PaperTwoLocalRestorationBound

end

/- Source module: Erdos390.Full.FullTiltPairChamber -/
section


/-!
# Full valuation tilt in the two-prime four-mark chamber

This is the paper-facing closure of the two-local restoration.  It combines

* the actual structured-cell omitted-score four-mark estimate,
* the exact `N_{r,s}/N_{0,0}` restoration identity,
* the arbitrary-modulus reciprocal fallback for every restoration term, and
* the uniform lower bound for the exact normalizer.

The conclusion concerns the genuine full valuation tilt over the genuine
structured cell.  No covariance estimate or analytic transfer is assumed.
-/

open Filter Topology

namespace Erdos390.Full.FullTiltPairChamber

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination ValuationCutoff
open PaperScaleMarkedCell OmittedTiltPairChamber OmittedTiltFallback
open TwoLocalRestoration TwoLocalPairRestoration
open TwoLocalRestorationBound PaperTwoLocalRestorationBound

noncomputable section





/-- The fallback density is positive for every positive physical upper
endpoint; the normalization `1 ≤ C` used by older wrappers is unnecessary. -/
theorem pairFallbackDensity_pos_of_pos (H : Pattern) {A C : ℝ}
    (hAC : A < C) (hC : 0 < C) :
    0 < pairFallbackDensity H A C := by
  unfold pairFallbackDensity
  exact div_pos (paperCellDensity_pos H hAC) (mul_pos (by norm_num) hC)









end

end Erdos390.Full.FullTiltPairChamber

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









theorem pairWeight_eq_single_mul (p q r s : ℕ) :
    pairWeight p q r s = singleWeight p r * singleWeight q s := by
  unfold pairWeight singleWeight
  ring

theorem pairWeight_nonneg (p q r s : ℕ) :
    0 ≤ pairWeight p q r s := by
  unfold pairWeight
  positivity









theorem localRestorationScale_nonneg {G k : ℝ}
    (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ localRestorationScale G k := by
  unfold localRestorationScale
  positivity

theorem pairProbabilityScale_nonneg {epsilon G k : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ pairProbabilityScale epsilon G k := by
  unfold pairProbabilityScale
  have hlocal := localRestorationScale_nonneg hG hk
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity

theorem pairCovarianceScale_nonneg {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ pairCovarianceScale E := by
  unfold pairCovarianceScale
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity



/-- Two pointwise coefficient-tail bounds imply a product-weighted bound
for the complete two-local restoration error. -/
theorem pairRestorationError_le_pairWeight
    {p q Ap Aq r s : ℕ} {etaP etaQ L₀ G G₀ k : ℝ}
    (hG : G ≤ G₀) (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hpTail : coefficientTail p Ap r etaP L₀ ≤
      k * (((r : ℝ) + 1) / (p : ℝ) ^ r))
    (hqTail : coefficientTail q Aq s etaQ L₀ ≤
      k * (((s : ℝ) + 1) / (q : ℝ) ^ s)) :
    pairRestorationError p q Ap Aq r s etaP etaQ L₀ G ≤
      localRestorationScale G₀ k * pairWeight p q r s := by
  let dp := coefficientTail p Ap r etaP L₀
  let dq := coefficientTail q Aq s etaQ L₀
  have hdp0 : 0 ≤ dp := coefficientTail_nonneg _ _ _ _ _
  have hdq0 : 0 ≤ dq := coefficientTail_nonneg _ _ _ _ _
  have hpden0 : 0 ≤ (p : ℝ) ^ r := by positivity
  have hqden0 : 0 ≤ (q : ℝ) ^ s := by positivity
  have hpInv0 : 0 ≤ 1 / (p : ℝ) ^ r := by positivity
  have hqInv0 : 0 ≤ 1 / (q : ℝ) ^ s := by positivity
  have hdp : dp ≤ k * (((r : ℝ) + 1) / (p : ℝ) ^ r) := hpTail
  have hdq : dq ≤ k * (((s : ℝ) + 1) / (q : ℝ) ^ s) := hqTail
  have hGdp : G * dp ≤
      G₀ * (k * (((r : ℝ) + 1) / (p : ℝ) ^ r)) :=
    mul_le_mul hG hdp hdp0 hG₀
  have hGdq : G * dq ≤
      G₀ * (k * (((s : ℝ) + 1) / (q : ℝ) ^ s)) :=
    mul_le_mul hG hdq hdq0 hG₀
  have htermP : G * dp * (1 / (q : ℝ) ^ s) ≤
      G₀ * k * pairWeight p q r s := by
    calc
      G * dp * (1 / (q : ℝ) ^ s) ≤
          (G₀ * (k * (((r : ℝ) + 1) / (p : ℝ) ^ r))) *
            (1 / (q : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_right hGdp hqInv0
      _ = (G₀ * k * ((r : ℝ) + 1) *
          (1 / (p : ℝ) ^ r) * (1 / (q : ℝ) ^ s)) := by ring
      _ ≤ (G₀ * k * ((r : ℝ) + 1) *
          (1 / (p : ℝ) ^ r) * (1 / (q : ℝ) ^ s)) *
            ((s : ℝ) + 1) := by
        have hbase : 0 ≤ G₀ * k * ((r : ℝ) + 1) *
            (1 / (p : ℝ) ^ r) * (1 / (q : ℝ) ^ s) := by positivity
        nlinarith
      _ = G₀ * k * pairWeight p q r s := by
        unfold pairWeight
        ring
  have htermQ : G * (1 / (p : ℝ) ^ r) * dq ≤
      G₀ * k * pairWeight p q r s := by
    calc
      G * (1 / (p : ℝ) ^ r) * dq = (G * dq) *
          (1 / (p : ℝ) ^ r) := by ring
      _ ≤ (G₀ * (k * (((s : ℝ) + 1) / (q : ℝ) ^ s))) *
          (1 / (p : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_right hGdq hpInv0
      _ = (G₀ * k * ((s : ℝ) + 1) *
          (1 / (q : ℝ) ^ s) * (1 / (p : ℝ) ^ r)) := by ring
      _ ≤ (G₀ * k * ((s : ℝ) + 1) *
          (1 / (q : ℝ) ^ s) * (1 / (p : ℝ) ^ r)) *
            ((r : ℝ) + 1) := by
        have hbase : 0 ≤ G₀ * k * ((s : ℝ) + 1) *
            (1 / (q : ℝ) ^ s) * (1 / (p : ℝ) ^ r) := by positivity
        nlinarith
      _ = G₀ * k * pairWeight p q r s := by
        unfold pairWeight
        ring
  have htermPQ : G * dp * dq ≤
      G₀ * k ^ 2 * pairWeight p q r s := by
    calc
      G * dp * dq ≤
          (G₀ * (k * (((r : ℝ) + 1) / (p : ℝ) ^ r))) *
            (k * (((s : ℝ) + 1) / (q : ℝ) ^ s)) :=
        mul_le_mul hGdp hdq hdq0 (by positivity)
      _ = G₀ * k ^ 2 * pairWeight p q r s := by
        unfold pairWeight
        ring
  unfold pairRestorationError localRestorationScale
  dsimp only [dp, dq] at htermP htermQ htermPQ
  calc
    _ ≤ G₀ * k * pairWeight p q r s +
        G₀ * k * pairWeight p q r s +
          G₀ * k ^ 2 * pairWeight p q r s :=
      add_le_add_three htermP htermQ htermPQ
    _ = G₀ * (2 * k + k ^ 2) * pairWeight p q r s := by ring

/-- A small algebraic adapter used for the main-times-restoration term.
Keeping this estimate separate makes all sign assumptions explicit. -/
theorem abs_mul_le_scaled_weight
    {a b R E dInv w : ℝ}
    (ha : |a| ≤ R * dInv) (hb₀ : 0 ≤ b) (hb : b ≤ E)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hdInv : 0 ≤ dInv)
    (hdInvw : dInv ≤ w) :
    |a| * b ≤ (R * E) * w := by
  have hprod : |a| * b ≤ (R * dInv) * E :=
    mul_le_mul ha hb hb₀ (mul_nonneg hR hdInv)
  have hscale : 0 ≤ R * E := mul_nonneg hR hE
  calc
    |a| * b ≤ (R * dInv) * E := hprod
    _ = (R * E) * dInv := by ring
    _ ≤ (R * E) * w := mul_le_mul_of_nonneg_left hdInvw hscale





/-- The explicit full-pair probability error is bounded by one scalar times
the natural product weight. -/
theorem fullPairChamberError_le_pairWeight
    (H : Pattern) {A C B : ℝ} {W n p q r s : ℕ}
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ) {G₀ k : ℝ}
    (hn : 1 < n) (hpBand : p ∈ primeBand n W)
    (hqBand : q ∈ primeBand n W)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4)
    (hepsilon : 0 ≤ epsilon n)
    (hc : 0 ≤ pairFallbackDensity H A C)
    (hG : paperPairFallbackConstant B C (pairFallbackDensity H A C) W n ≤ G₀)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hcoef : ∀ z ∈ primeBand n W, ∀ u : ℕ,
      coefficientTail z (ValuationCutoff.valuationCutoff z (physicalBound C n))
        u (eta z) (L n) ≤
          k * (((u : ℝ) + 1) / (z : ℝ) ^ u)) :
    fullPairChamberError H A C B W n p q r s eta epsilon ≤
      pairProbabilityScale (epsilon n) G₀ k * pairWeight p q r s := by
  let G := paperPairFallbackConstant B C (pairFallbackDensity H A C) W n
  let Ap := ValuationCutoff.valuationCutoff p (physicalBound C n)
  let Aq := ValuationCutoff.valuationCutoff q (physicalBound C n)
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hG0 : 0 ≤ G := paperPairFallbackConstant_nonneg _ _ _ _ _ hc
  have hrs := pairRestorationError_le_pairWeight hG hG₀ hk
    (hcoef p hpBand r) (hcoef q hqBand s)
  have h00raw := pairRestorationError_le_pairWeight hG hG₀ hk
    (hcoef p hpBand 0) (hcoef q hqBand 0)
  have hweight00 : pairWeight p q 0 0 = 1 := by
    simp [pairWeight]
  have h00 : pairRestorationError p q Ap Aq 0 0
      (eta p) (eta q) (L n) G ≤ localRestorationScale G₀ k := by
    simpa only [Ap, Aq, G, hweight00, mul_one] using h00raw
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hmainRaw := paperDivisibilityMain_nonneg_le hn hDpos hD4
  have hmain : |paperDivisibilityMain n (pairPower p q r s)| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
    rw [abs_of_nonneg hmainRaw.1]
    convert hmainRaw.2 using 1
    all_goals
      simp only [pairPower, Nat.cast_mul, Nat.cast_pow]
      ring
  have hweightOne :
      1 / ((p : ℝ) ^ r * (q : ℝ) ^ s) ≤ pairWeight p q r s := by
    unfold pairWeight
    have hden0 : 0 ≤ (p : ℝ) ^ r * (q : ℝ) ^ s := by positivity
    have hnum : (1 : ℝ) ≤ ((r : ℝ) + 1) * ((s : ℝ) + 1) := by
      nlinarith [show (0 : ℝ) ≤ r by positivity,
        show (0 : ℝ) ≤ s by positivity]
    exact div_le_div_of_nonneg_right hnum hden0
  have heps : epsilon n / (pairPower p q r s : ℝ) ≤
      epsilon n * pairWeight p q r s := by
    norm_num only [pairPower, Nat.cast_mul, Nat.cast_pow]
    have hmul := mul_le_mul_of_nonneg_left hweightOne hepsilon
    simpa [div_eq_mul_inv] using hmul
  calc
    fullPairChamberError H A C B W n p q r s eta epsilon =
        2 * (pairRestorationError p q Ap Aq r s
            (eta p) (eta q) (L n) G +
          epsilon n / (pairPower p q r s : ℝ) +
          |paperDivisibilityMain n (pairPower p q r s)| *
            pairRestorationError p q Ap Aq 0 0
              (eta p) (eta q) (L n) G) := by
      rfl
    _ ≤ 2 * (localRestorationScale G₀ k * pairWeight p q r s +
        epsilon n * pairWeight p q r s +
        ((1 / DickmanBasic.rho DickmanBasic.U) *
          localRestorationScale G₀ k) * pairWeight p q r s) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_three hrs heps
          (abs_mul_le_scaled_weight
            (by simpa [div_eq_mul_inv] using hmain)
            (pairRestorationError_nonneg _ _ _ _ _ _ _ _ _ _ hG0) h00
            (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)
            (localRestorationScale_nonneg hG₀ hk) (by positivity)
            hweightOne))
        (by norm_num)
    _ = pairProbabilityScale (epsilon n) G₀ k *
        pairWeight p q r s := by
      unfold pairProbabilityScale
      ring



end

end Erdos390.Full.PaperPrimePowerChamberError

end

/- Source module: Erdos390.Full.PaperPrimePowerAuxiliaryPrime -/
section


/-!
# A uniform auxiliary prime for diagonal restoration

The diagonal probability is recovered from the two-local restoration by
giving each row prime a distinct auxiliary band prime with exponent zero.
Two fixed primes above the cutoff suffice once the moving band reaches them.
-/

open Filter

namespace Erdos390.Full.PaperPrimePowerAuxiliaryPrime

open ArithmeticModel HeadPattern

noncomputable section



/-- Every prime in the moving band is coprime to the head modulus as soon as
all primes occurring in the head pattern lie at or below the cutoff.  Unlike
`H.modulus ≤ W`, this is compatible with prescribing every prime `q ≤ W`. -/
theorem coprime_modulus_of_mem_primeBand_of_headSupport
    (H : Pattern) {n W p : ℕ}
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W)
    (hpBand : p ∈ primeBand n W) : Nat.Coprime p H.modulus := by
  rw [Pattern.modulus, Nat.coprime_prod_right_iff]
  intro q hq
  have hp := prime_of_mem_primeBand hpBand
  have hqPrime := H.prime_mem q hq
  have hpGt : W < p := cutoff_lt_of_mem_primeBand hpBand
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact (Nat.not_lt_of_ge (hHeadLe p hq)) hpGt
  exact (Nat.coprime_primes hp hqPrime).mpr hpq



/-- Two fixed primes above `W`; the selected one is always different from
the current row prime. -/
theorem exists_eventually_auxiliaryPrime
    (W : ℕ) :
    ∃ q₀ q₁ : ℕ, ∃ aux : ℕ → ℕ,
      q₀.Prime ∧ q₁.Prime ∧ W < q₀ ∧ q₀ < q₁ ∧
      aux = (fun p ↦ if p = q₀ then q₁ else q₀) ∧
      ∀ᶠ n : ℕ in atTop,
        q₀ ∈ primeBand n W ∧ q₁ ∈ primeBand n W ∧
          ∀ p ∈ primeBand n W,
            aux p ∈ (primeBand n W).erase p := by
  obtain ⟨q₀, hWq₀, hq₀⟩ := Nat.exists_infinite_primes (W + 1)
  obtain ⟨q₁, hq₀q₁, hq₁⟩ := Nat.exists_infinite_primes (q₀ + 1)
  let aux : ℕ → ℕ := fun p ↦ if p = q₀ then q₁ else q₀
  have hWltq₀ : W < q₀ := by omega
  have hq₀ltq₁ : q₀ < q₁ := by omega
  have hyTop : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hreach : ∀ᶠ n : ℕ in atTop, (q₁ : ℝ) ≤ y n :=
    hyTop.eventually (eventually_ge_atTop (q₁ : ℝ))
  refine ⟨q₀, q₁, aux, hq₀, hq₁, hWltq₀, hq₀ltq₁, rfl, ?_⟩
  filter_upwards [hreach] with n hqn
  have hq₁Y : q₁ ≤ yNat n := Nat.le_floor hqn
  have hq₀Y : q₀ ≤ yNat n := hq₀ltq₁.le.trans hq₁Y
  have hq₀Band : q₀ ∈ primeBand n W :=
    mem_primeBand.mpr ⟨hq₀, hWltq₀, hq₀Y⟩
  have hq₁Band : q₁ ∈ primeBand n W :=
    mem_primeBand.mpr ⟨hq₁, hWltq₀.trans hq₀ltq₁, hq₁Y⟩
  refine ⟨hq₀Band, hq₁Band, ?_⟩
  intro p hpBand
  by_cases hpq₀ : p = q₀
  · have hq₁p : q₁ ≠ p := by omega
    simpa only [aux, if_pos hpq₀] using
      (Finset.mem_erase.mpr ⟨hq₁p, hq₁Band⟩)
  · have hq₀p : q₀ ≠ p := by exact fun h ↦ hpq₀ h.symm
    simpa only [aux, if_neg hpq₀] using
      (Finset.mem_erase.mpr ⟨hq₀p, hq₀Band⟩)

end

end Erdos390.Full.PaperPrimePowerAuxiliaryPrime

end

/- Source module: Erdos390.Full.FixedFiniteMixtureFullUniform -/
section


/-!
# Full uniform Lemma 7.5 for a fixed finite family of actual cells

This file specializes the marked-cell and full-tilt asymptotics on every
member of a fixed finite family, takes finite common majorants, and applies
the exact tagged-mixture theorem.  No desired covariance or tail estimate
is assumed by the final export.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.FixedFiniteMixtureFullUniform

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPairHarmonicRate FullTiltPrimePowerFallback
open DickmanFourMarkProductKernel PaperScaleMarkedCell
open PaperTwoLocalRestorationBound LocalFugacityBounds
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerLemma75 PaperPrimePowerGenericAggregation
open FixedFiniteMixtureLemma75 PaperValuationCutoff ValuationCutoff
open PrimeSums

noncomputable section





theorem pairProbabilityScale_le_primePowerChamberRemainder
    {epsilon G k : ℝ} (hepsilon : 0 ≤ epsilon)
    (hG : 0 ≤ G) (hk : 0 ≤ k) :
    pairProbabilityScale epsilon G k ≤
      primePowerChamberRemainder epsilon G k := by
  unfold primePowerChamberRemainder aggregateChamberScale
  have hE := pairProbabilityScale_nonneg hepsilon hG hk
  have hcov := pairCovarianceScale_nonneg hE
  linarith



variable {Cell : Type*} [Fintype Cell]







end

end Erdos390.Full.FixedFiniteMixtureFullUniform

end

/- Source module: Erdos390.Full.FixedFiniteMixtureSignedSquarefree -/
section


/-!
# Signed squarefree profiles for a fixed finite family of cells

The prime-power conclusion of paper Lemma 7.5 is an absolute tail estimate.
The arithmetic inverse in Lemma 8.4 instead needs the signed one- and
two-divisor profiles before covariance is formed.  The proof of the former
already constructs a common finite-family profile with one harmonic loss to
spare.  This file exports that stronger intermediate conclusion explicitly,
without taking it as a hypothesis.
-/

open Filter Topology

namespace Erdos390.Full.FixedFiniteMixtureSignedSquarefree

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPairHarmonicRate
open PaperTwoLocalRestorationBound LocalFugacityBounds
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerRemainderRate PaperScaleMarkedCell
open PaperValuationCutoff PaperPrimePowerAuxiliaryPrime
open FixedFiniteMixtureFullUniform

noncomputable section

variable {Cell : Type*} [Fintype Cell]

/-- A single signed marked-profile error works for every cell in a fixed
finite family, every pair of moving primes and every four-mark exponent
pair.  It tends to zero even after multiplication by `log (L n)`, which is
the precise margin required by the moving-low sharp row.

The coefficient box is selected only after `W`; all dependence on that box
is confined to `signedError` and the eventual threshold.

This positive-endpoint core only assumes strict positivity of `C`; the
paper-facing wrapper below retains its earlier normalization `1 ≤ C`. -/
theorem exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hC_le : ∀ c, C c ≤ Cmax) :
    ∀ W : ℕ, 1 < W →
      (∀ c, ∀ p ∈ (H c).primes, p ≤ W) →
    ∀ B : ℝ, 0 ≤ B →
      ∃ signedError : ℕ → ℝ,
        (∀ n, 0 ≤ signedError n) ∧
        Tendsto signedError atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ signedError n * Real.log (L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := fun c ↦ structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          (∀ c, (S c).Nonempty) ∧
            ∀ hS : ∀ c, (S c).Nonempty,
            let law := fun c ↦ widen
              (valuationTilt (H c) (physicalBound (A c) n)
                (physicalBound (C c) n) (yNat n) (hS c)
                (primeBand n W) eta (L n))
              (physicalBound_mono (hC_le c) n)
            (∀ c p, p ∈ primeBand n W →
              ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
              pairPower p q r s ≤ yNat n ^ 4 →
              |(law c).probability.expect
                  (fun omega ↦ divInd (pairPower p q r s)
                    ((law c).value omega)) -
                paperDivisibilityMain n (pairPower p q r s)| ≤
                  signedError n * pairWeight p q r s) ∧
            (∀ c p, p ∈ primeBand n W →
              |(law c).probability.expect
                  (fun omega ↦ divInd p ((law c).value omega)) -
                paperDivisibilityMain n p| ≤
                  signedError n * singleWeight p 1) := by
  intro W hW hHW B hB
  have hpairExists : ∀ c, ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto epsilon atTop (nhds 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n) ^ 2)
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n p q r s : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        q ∈ (primeBand n W).erase p →
        pairPower p q r s ≤ yNat n ^ 4 →
        Nat.Coprime p (H c).modulus → Nat.Coprime q (H c).modulus →
        (∀ z ∈ primeBand n W, |eta z| ≤ B) →
        let S := structuredCell (H c) (physicalBound (A c) n)
          (physicalBound (C c) n) (yNat n)
        S.Nonempty ∧ ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
              (fun m : S ↦ valuationScore (primeBand n W) eta (L n) m)).expect
              (fun m : S ↦ divInd (pairPower p q r s) m) -
            paperDivisibilityMain n (pairPower p q r s)| ≤
          fullPairChamberError (H c) (A c) (C c) B W n p q r s
            eta epsilon := by
    intro c
    exact exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate
      (H c) (hA c) (hAC c) (hC c) B W hB hW
  choose epsilon hepsilonData using hpairExists
  have hepsilon0 (c : Cell) : ∀ n, 0 ≤ epsilon c n :=
    (hepsilonData c).1
  have hepsilonT (c : Cell) : Tendsto (epsilon c) atTop (nhds 0) :=
    (hepsilonData c).2.1
  have hepsilonRate (c : Cell) : Tendsto
      (fun n : ℕ ↦ epsilon c n * Real.log (L n)) atTop (nhds 0) :=
    (hepsilonData c).2.2.1
  have hepsilonRateSq (c : Cell) : Tendsto
      (fun n : ℕ ↦ epsilon c n * Real.log (L n) ^ 2) atTop (nhds 0) :=
    (hepsilonData c).2.2.2.1
  choose Npair hpairRaw using fun c ↦ (hepsilonData c).2.2.2.2
  let cden : Cell → ℝ := fun c ↦ pairFallbackDensity (H c) (A c) (C c)
  let G₀ : Cell → ℝ := fun c ↦ paperPairFallbackCeiling B (cden c) W
  let cellRemainder : Cell → ℕ → ℝ := fun c n ↦
    primePowerChamberRemainder (epsilon c n) (G₀ c)
      (coefficientScale B W n)
  let signedError : ℕ → ℝ := fun n ↦ ∑ c, |cellRemainder c n|
  have hcellRemainderT (c : Cell) :
      Tendsto (cellRemainder c) atTop (nhds 0) := by
    simpa only [cellRemainder] using
      (tendsto_primePowerChamberRemainder_zero_and_rate
        (epsilon c) (G₀ c) B W (hepsilonT c) (hepsilonRate c)).1
  have hcellRemainderRate (c : Cell) : Tendsto
      (fun n : ℕ ↦ cellRemainder c n * Real.log (L n))
        atTop (nhds 0) := by
    simpa only [cellRemainder] using
      (tendsto_primePowerChamberRemainder_zero_and_rate
        (epsilon c) (G₀ c) B W (hepsilonT c) (hepsilonRate c)).2
  have hsignedErrorT : Tendsto signedError atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ (hcellRemainderT c).abs)
    simpa only [signedError, abs_zero, Finset.sum_const_zero] using hsum
  have hlogLNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) := by
    have hLTop : Tendsto L atTop atTop := by
      simpa only [L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hLge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ L n :=
      hLTop.eventually (eventually_ge_atTop 1)
    filter_upwards [hLge] with n hn
    exact Real.log_nonneg hn
  have hcellAbsRate (c : Cell) : Tendsto
      (fun n : ℕ ↦ |cellRemainder c n| * Real.log (L n))
        atTop (nhds 0) := by
    have habs := (hcellRemainderRate c).abs
    have habs0 : Tendsto
        (fun n : ℕ ↦ |cellRemainder c n * Real.log (L n)|)
          atTop (nhds 0) := by simpa only [abs_zero] using habs
    apply habs0.congr'
    filter_upwards [hlogLNonneg] with n hlog
    rw [abs_mul, abs_of_nonneg hlog]
  have hsignedErrorRate : Tendsto
      (fun n : ℕ ↦ signedError n * Real.log (L n))
        atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ hcellAbsRate c)
    have hsum0 : Tendsto
        (fun n : ℕ ↦ ∑ c, |cellRemainder c n| * Real.log (L n))
          atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    dsimp only [signedError]
    rw [Finset.sum_mul]
  have hcden (c : Cell) : 0 < cden c := by
    dsimp only [cden]
    exact pairFallbackDensity_pos_of_pos (H c) (hAC c) (hC c)
  have hG₀ (c : Cell) : 0 < G₀ c := by
    dsimp only [G₀]
    exact paperPairFallbackCeiling_pos B (cden c) W (hcden c)
  have hNpairEvent : ∀ᶠ n : ℕ in atTop, ∀ c, Npair c ≤ n := by
    rw [Filter.eventually_all]
    intro c
    exact eventually_ge_atTop (Npair c)
  have hGEvent : ∀ᶠ n : ℕ in atTop, ∀ c,
      paperPairFallbackConstant B (C c) (cden c) W n ≤ G₀ c := by
    rw [Filter.eventually_all]
    intro c
    simpa only [G₀] using eventually_paperPairFallbackConstant_le
      B (C c) (cden c) W hB (hC c) (hcden c) hW
  have hcoefEvent : ∀ᶠ n : ℕ in atTop, ∀ c,
      ∀ p ∈ primeBand n W, ∀ eta₀ : ℝ, |eta₀| ≤ B → ∀ r : ℕ,
      coefficientTail p (ValuationCutoff.valuationCutoff p
          (physicalBound (C c) n)) r eta₀ (L n) ≤
        coefficientScale B W n * (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
    rw [Filter.eventually_all]
    intro c
    simpa only [coefficientScale] using
      eventually_coefficientTail_le_of_pos B (C c) W hB (hC c) hW
  obtain ⟨q₀, q₁, aux, _, _, _, hq₀q₁, _, hauxEvent⟩ :=
    PaperPrimePowerAuxiliaryPrime.exists_eventually_auxiliaryPrime W
  have hfinal : ∀ᶠ n : ℕ in atTop, ∀ eta : ℕ → ℝ,
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := fun c ↦ structuredCell (H c)
        (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
      (∀ c, (S c).Nonempty) ∧
        ∀ hS : ∀ c, (S c).Nonempty,
        let law := fun c ↦ widen
          (valuationTilt (H c) (physicalBound (A c) n)
            (physicalBound (C c) n) (yNat n) (hS c)
            (primeBand n W) eta (L n))
          (physicalBound_mono (hC_le c) n)
        (∀ c p, p ∈ primeBand n W →
          ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
          pairPower p q r s ≤ yNat n ^ 4 →
          |(law c).probability.expect
              (fun omega ↦ divInd (pairPower p q r s)
                ((law c).value omega)) -
            paperDivisibilityMain n (pairPower p q r s)| ≤
              signedError n * pairWeight p q r s) ∧
        (∀ c p, p ∈ primeBand n W →
          |(law c).probability.expect
              (fun omega ↦ divInd p ((law c).value omega)) -
            paperDivisibilityMain n p| ≤
              signedError n * singleWeight p 1) := by
    filter_upwards [Filter.eventually_gt_atTop 1, hNpairEvent,
      hGEvent, hcoefEvent, hauxEvent]
      with n hn hNpairn hGn hcoefn hauxn
    intro eta heta
    obtain ⟨hq₀Band, hq₁Band, hauxn⟩ := hauxn
    have hq₁Erase : q₁ ∈ (primeBand n W).erase q₀ :=
      Finset.mem_erase.mpr ⟨hq₀q₁.ne', hq₁Band⟩
    let S := fun c ↦ structuredCell (H c)
      (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
    have hSnonempty : ∀ c, (S c).Nonempty := by
      intro c
      have hq₀Head := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hq₀Band
      have hq₁Head := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hq₁Band
      have hyPos : 0 < yNat n :=
        (prime_of_mem_primeBand hq₀Band).pos.trans_le
          (le_yNat_of_mem_primeBand hq₀Band)
      have hzero : pairPower q₀ q₁ 0 0 ≤ yNat n ^ 4 := by
        simpa only [pairPower, pow_zero, mul_one] using
          (one_le_pow₀ (show 1 ≤ yNat n from hyPos))
      have hseed := hpairRaw c eta (hNpairn c) hq₀Band hq₁Erase
        hzero hq₀Head hq₁Head heta
      simpa only [S] using hseed.1
    refine ⟨hSnonempty, ?_⟩
    intro hS
    let baseLaw := fun c ↦
      valuationTilt (H c) (physicalBound (A c) n)
        (physicalBound (C c) n) (yNat n) (hS c)
        (primeBand n W) eta (L n)
    let law := fun c ↦ widen (baseLaw c)
      (physicalBound_mono (hC_le c) n)
    have hk : 0 ≤ coefficientScale B W n := by
      unfold coefficientScale
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) hB) (L_pos hn).le)
        (Real.exp_pos _).le
    have hprofileCell : ∀ c p, p ∈ primeBand n W →
        ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
        pairPower p q r s ≤ yNat n ^ 4 →
        |(law c).probability.expect
            (fun omega ↦ divInd (pairPower p q r s)
              ((law c).value omega)) -
          paperDivisibilityMain n (pairPower p q r s)| ≤
          signedError n * pairWeight p q r s := by
      intro c p hpBand q hqErase r s hD4
      have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
      have hpHead := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hpBand
      have hqHead := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hqBand
      have hraw := (hpairRaw c eta (hNpairn c) hpBand hqErase hD4
        hpHead hqHead heta).2 (hS c)
      have herr := fullPairChamberError_le_pairWeight
        (H c) eta (epsilon c) hn hpBand hqBand hD4
        (hepsilon0 c n)
        (show 0 ≤ pairFallbackDensity (H c) (A c) (C c) by
          exact (hcden c).le)
        (by simpa only [cden, G₀] using hGn c) (hG₀ c).le hk
        (fun z hz u ↦ hcoefn c z hz (eta z) (heta z hz) u)
      have hprobToCell :
          pairProbabilityScale (epsilon c n) (G₀ c)
              (coefficientScale B W n) ≤ cellRemainder c n :=
        pairProbabilityScale_le_primePowerChamberRemainder
          (hepsilon0 c n) (hG₀ c).le hk
      have hcellToProfile : cellRemainder c n ≤ signedError n := by
        calc
          cellRemainder c n ≤ |cellRemainder c n| := le_abs_self _
          _ ≤ ∑ d, |cellRemainder d n| := by
            exact Finset.single_le_sum
              (fun d hd ↦ abs_nonneg (cellRemainder d n))
              (Finset.mem_univ c)
          _ = signedError n := rfl
      have hscale := mul_le_mul_of_nonneg_right
        (hprobToCell.trans hcellToProfile) (pairWeight_nonneg p q r s)
      have hbound := hraw.trans (herr.trans hscale)
      simpa only [law, baseLaw, widen_probability, widen_value,
        valuationTilt_probability, valuationTilt_value] using hbound
    have hsingleProfile : ∀ c p, p ∈ primeBand n W →
        |(law c).probability.expect
            (fun omega ↦ divInd p ((law c).value omega)) -
          paperDivisibilityMain n p| ≤
          signedError n * singleWeight p 1 := by
      intro c p hpBand
      let q := aux p
      have hqErase : q ∈ (primeBand n W).erase p := hauxn p hpBand
      have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
      have hyPos : 0 < yNat n :=
        (prime_of_mem_primeBand hpBand).pos.trans_le hpY
      have hD4 : p ≤ yNat n ^ 4 := by
        calc
          p ≤ yNat n := hpY
          _ ≤ yNat n ^ 4 := by
            nlinarith [sq_nonneg ((yNat n : ℤ) ^ 2 - 1)]
      have hpair := hprofileCell c p hpBand q hqErase 1 0
        (by simpa only [pairPower, pow_one, pow_zero, mul_one] using hD4)
      simpa only [pairPower, pow_one, pow_zero, mul_one,
        pairWeight_eq_single_mul, singleWeight, Nat.cast_zero,
        zero_add, div_one, mul_one] using hpair
    exact ⟨hprofileCell, hsingleProfile⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨signedError, fun n ↦ Finset.sum_nonneg
    (fun c hc ↦ abs_nonneg (cellRemainder c n)),
    hsignedErrorT, hsignedErrorRate, N₀, ?_⟩
  intro n eta hn heta
  exact hN₀ n hn eta heta



end

end Erdos390.Full.FixedFiniteMixtureSignedSquarefree

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal001_003.{u_1} := by
  exact @Erdos390.Full.FixedFiniteMixtureSignedSquarefree.exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos
