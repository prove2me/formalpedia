-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_uniform_rawSmoothBasePool_valuation_mean_profile_paperRate_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:28:53.593164+00:00
-- url     : https://prove2.me/submissions/7231af2c-9425-4b4d-92e7-8159b3280efd

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
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_movingPrefix_valuation_mean_profile_paperRate_of_fraction_compact


section
theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_valuation_mean_profile_paperRate_of_fraction : Erdos390.RemainingAnalyticGoal007_009 := @Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_valuation_mean_profile_paperRate_of_fraction_compact
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



theorem factorization_factor (q : ℕ) :
    P.factor.factorization q =
      if q ∈ P.primes then P.exponent q else 0 := by
  classical
  rw [factor, Nat.factorization_prod_apply]
  · calc
      ∑ p ∈ P.primes, (p ^ P.exponent p).factorization q =
          ∑ p ∈ P.primes, if p = q then P.exponent p else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(P.prime_mem p hp).factorization_pow]
            simp [Finsupp.single_apply]
      _ = if q ∈ P.primes then P.exponent q else 0 := by
        simp [eq_comm]
  · intro p hp
    exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem factor_dvd_of_matches {m : ℕ} (hm : m ≠ 0) (hmatch : P.Matches m) :
    P.factor ∣ m := by
  rw [← Nat.factorization_le_iff_dvd P.factor_ne_zero hm]
  intro q
  rw [P.factorization_factor q]
  split_ifs with hq
  · exact (hmatch q hq).ge
  · exact Nat.zero_le _

theorem exponent_le_of_factor_dvd {m p : ℕ} (hm : m ≠ 0)
    (hfac : P.factor ∣ m) (hp : p ∈ P.primes) :
    P.exponent p ≤ m.factorization p := by
  have hle := (Nat.factorization_le_iff_dvd P.factor_ne_zero hm).mpr hfac p
  simpa [P.factorization_factor p, hp] using hle

/-- Prescribing all head valuations is exactly the condition that the forced
prime-power factor divides `m` and that the remaining quotient contains none
of the head primes.  This is the exact finite identity to which Möbius
inclusion--exclusion is later applied. -/
theorem matches_iff_factor_dvd_and_coprime {m : ℕ} (hm : m ≠ 0) :
    P.Matches m ↔
      P.factor ∣ m ∧ Nat.Coprime (m / P.factor) P.modulus := by
  constructor
  · intro hmatch
    have hfac : P.factor ∣ m := P.factor_dvd_of_matches hm hmatch
    refine ⟨hfac, ?_⟩
    rw [modulus, Nat.coprime_prod_right_iff]
    intro p hp
    apply Nat.Coprime.symm
    apply (P.prime_mem p hp).coprime_iff_not_dvd.mpr
    intro hpdvd
    have hquot_ne : m / P.factor ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hfac)
        (Nat.pos_of_ne_zero P.factor_ne_zero)).ne'
    have hpos := (P.prime_mem p hp).factorization_pos_of_dvd hquot_ne hpdvd
    have hdiv : (m / P.factor).factorization p =
        m.factorization p - P.factor.factorization p := by
      simpa only [Finsupp.sub_apply] using
        congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_div hfac)
    rw [P.factorization_factor p, if_pos hp, hmatch p hp] at hdiv
    have hzero : (m / P.factor).factorization p = 0 := by
      simpa using hdiv
    omega
  · rintro ⟨hfac, hcop⟩
    intro p hp
    have hhead : Nat.Coprime (m / P.factor) p := by
      rw [modulus, Nat.coprime_prod_right_iff] at hcop
      exact hcop p hp
    have hnotdvd : ¬ p ∣ m / P.factor :=
      (P.prime_mem p hp).coprime_iff_not_dvd.mp hhead.symm
    have hzero : (m / P.factor).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnotdvd
    have hdiv : (m / P.factor).factorization p =
        m.factorization p - P.factor.factorization p := by
      simpa only [Finsupp.sub_apply] using
        congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_div hfac)
    rw [P.factorization_factor p, if_pos hp] at hdiv
    have hupper : m.factorization p ≤ P.exponent p := by
      apply Nat.sub_eq_zero_iff_le.mp
      exact hdiv.symm.trans hzero
    exact Nat.le_antisymm hupper (P.exponent_le_of_factor_dvd hm hfac hp)















end Pattern

end Erdos390.Full.HeadPattern

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





/-- The elementary logarithmic comparison `log n / n → 0`, made public
for later upper-bound estimates. -/
theorem log_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

/-- The second-order scale `n / log n` diverges to infinity. -/
theorem secondOrderScale_tendsto_atTop :
    Tendsto secondOrderScale atTop atTop := by
  have hpos :
      ∀ᶠ n : ℕ in atTop,
        0 < Real.log (n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (by positivity)
  have hright :
      Tendsto
        (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨log_natCast_div_natCast_tendsto_zero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦ by
    change (Real.log (n : ℝ) / (n : ℝ))⁻¹ =
      secondOrderScale n
    rw [secondOrderScale, inv_div]

/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

/-- Eventually the second-order scale is strictly positive. -/
theorem eventually_secondOrderScale_pos :
    ∀ᶠ n : ℕ in atTop, 0 < secondOrderScale n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact secondOrderScale_pos hn

/-- The second-order scale is sublinear. -/
theorem secondOrderScale_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ secondOrderScale n / (n : ℝ))
      atTop (nhds 0) := by
  have hinvLog :
      Tendsto (fun n : ℕ ↦ 1 / Real.log (n : ℝ))
        atTop (nhds 0) := by
    simpa only [one_div] using
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  apply hinvLog.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [secondOrderScale]
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  have hlogNe : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp





/-- Ceiling changes `c n/log n` only by a negligible relative error. -/
theorem upperTailLength_normalized_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailLength c n : ℝ) / secondOrderScale n)
      atTop (nhds c) := by
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc.le).comp
      secondOrderScale_tendsto_atTop

/-- The chosen upper tail is `o(n)`. -/
theorem upperTailLength_ratio_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hmul :=
    (upperTailLength_normalized_tendsto hc).mul
      secondOrderScale_ratio_tendsto_zero
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hscaleNe : secondOrderScale n ≠ 0 := hscale.ne'
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  field_simp





















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CompleteRoughDecomposition -/
section


/-!
# Complete rough/smooth decomposition

The complete rough label retains exactly the prime-power coordinates above
`y`.  This file defines the complementary literal quotient and proves that
the two pieces recover the original natural number, with exact complementary
factorizations and no auxiliary decomposition hypothesis.
-/

namespace Erdos390.WholePaper

noncomputable section



/-! ## Positivity, divisibility, and product recovery -/

/-- A complete rough label is always positive, including for `a = 0`, when
the empty factorization gives label `1`. -/
theorem completeRoughLabel_pos (y a : ℕ) :
    0 < completeRoughLabel y a := by
  rw [completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp

theorem completeRoughLabel_ne_zero (y a : ℕ) :
    completeRoughLabel y a ≠ 0 :=
  (completeRoughLabel_pos y a).ne'

/-- Literal Finsupp form of the high-prime factorization. -/
theorem completeRoughLabel_factorization_eq_filter_gt (y a : ℕ) :
    (completeRoughLabel y a).factorization =
      a.factorization.filter (fun p ↦ y < p) := by
  simpa only [completeRoughSignature] using
    completeRoughLabel_factorization y a

/-- Coordinate form of the exact high-prime factorization. -/
theorem completeRoughLabel_factorization_apply (y a p : ℕ) :
    (completeRoughLabel y a).factorization p =
      if y < p then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeRoughLabel_factorization_eq_filter_gt y a)
  simpa only [Finsupp.filter_apply] using h

/-- The retained high-prime product is a literal divisor of the original
number. -/
theorem completeRoughLabel_dvd (y a : ℕ) :
    completeRoughLabel y a ∣ a := by
  by_cases ha : a = 0
  · rw [ha]
    exact dvd_zero _
  · rw [← Nat.factorization_le_iff_dvd
      (completeRoughLabel_ne_zero y a) ha,
      completeRoughLabel_factorization_eq_filter_gt]
    intro p
    rw [Finsupp.filter_apply]
    split_ifs <;> simp

/-- The requested multiplication direction: the original number is the
rough label times its literal complementary quotient. -/
theorem completeRough_decomposition (y a : ℕ) :
    a = completeRoughLabel y a * completeSmoothPart y a := by
  calc
    a = a / completeRoughLabel y a * completeRoughLabel y a :=
      (Nat.div_mul_cancel (completeRoughLabel_dvd y a)).symm
    _ = completeRoughLabel y a * (a / completeRoughLabel y a) :=
      Nat.mul_comm _ _
    _ = completeRoughLabel y a * completeSmoothPart y a := rfl



/-! ## The complementary low-prime factorization -/

/-- The quotient retains exactly the complementary coordinates `p ≤ y`. -/
theorem completeSmoothPart_factorization_eq_filter_le (y a : ℕ) :
    (completeSmoothPart y a).factorization =
      a.factorization.filter (fun p ↦ p ≤ y) := by
  rw [completeSmoothPart,
    Nat.factorization_div (completeRoughLabel_dvd y a),
    completeRoughLabel_factorization_eq_filter_gt]
  ext p
  simp only [Finsupp.filter_apply]
  by_cases hpLow : p ≤ y
  · have hpNotHigh : ¬y < p := Nat.not_lt_of_ge hpLow
    simp [hpLow, hpNotHigh]
  · have hpHigh : y < p := Nat.lt_of_not_ge hpLow
    simp [hpLow, hpHigh]

/-- Coordinate form of the exact low-prime factorization. -/
theorem completeSmoothPart_factorization_apply (y a p : ℕ) :
    (completeSmoothPart y a).factorization p =
      if p ≤ y then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeSmoothPart_factorization_eq_filter_le y a)
  simpa only [Finsupp.filter_apply] using h

/-- Nonzero high-part coordinates lie strictly above the cutoff. -/
theorem completeRoughLabel_factorization_support
    {y a p : ℕ}
    (hp : (completeRoughLabel y a).factorization p ≠ 0) :
    y < p := by
  rw [completeRoughLabel_factorization_apply] at hp
  by_contra hpHigh
  simp [hpHigh] at hp

/-- Nonzero smooth-part coordinates lie weakly below the cutoff. -/
theorem completeSmoothPart_factorization_support
    {y a p : ℕ}
    (hp : (completeSmoothPart y a).factorization p ≠ 0) :
    p ≤ y := by
  rw [completeSmoothPart_factorization_apply] at hp
  by_contra hpLow
  simp [hpLow] at hp

/-- Every prime divisor of the complete rough label is above `y`. -/
theorem prime_dvd_completeRoughLabel_gt
    {y a p : ℕ} (hp : p.Prime)
    (hpDvd : p ∣ completeRoughLabel y a) :
    y < p := by
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeRoughLabel_ne_zero y a) hpDvd
  exact completeRoughLabel_factorization_support hfactorPos.ne'

/-- For a positive original number, the complementary quotient is positive. -/
theorem completeSmoothPart_pos {y a : ℕ} (ha : 0 < a) :
    0 < completeSmoothPart y a := by
  rw [completeSmoothPart]
  apply Nat.div_pos
  · exact Nat.le_of_dvd ha (completeRoughLabel_dvd y a)
  · exact completeRoughLabel_pos y a

/-- For a positive original number, the complementary quotient is literally
`(y+1)`-smooth in Mathlib's positive-number convention. -/
theorem completeSmoothPart_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeSmoothPart y a ∈ Nat.smoothNumbers (y + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpDvd
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeSmoothPart_pos ha).ne' hpDvd
  have hpLow : p ≤ y :=
    completeSmoothPart_factorization_support hfactorPos.ne'
  omega

/-! ## Uniqueness and the smooth-label criterion -/



/-- For positive `a`, the rough label is `1` exactly when `a` is
`(y+1)`-smooth. -/
theorem completeRoughLabel_eq_one_iff_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeRoughLabel y a = 1 ↔
      a ∈ Nat.smoothNumbers (y + 1) := by
  constructor
  · intro hlabel
    have haPart : a = completeSmoothPart y a := by
      simpa only [hlabel, one_mul] using
        completeRough_decomposition y a
    rw [haPart]
    exact completeSmoothPart_mem_smoothNumbers ha
  · intro haSmooth
    by_contra hlabel
    obtain ⟨p, hp, hpDvdLabel⟩ :=
      Nat.exists_prime_and_dvd hlabel
    have hpHigh : y < p :=
      prime_dvd_completeRoughLabel_gt hp hpDvdLabel
    have hpDvdA : p ∣ a :=
      hpDvdLabel.trans (completeRoughLabel_dvd y a)
    have hpLow :=
      (Nat.mem_smoothNumbers').mp haSmooth p hp hpDvdA
    omega



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector -/
section


/-!
# One-shot Section 8 orchestration for the two zero-head cells

This file joins the three already audited layers of the literal Section 8
construction:

* the analytic ledger gives the `q0` and integer-height asymptotics;
* the two-zero-cell producer realizes the height change by `-d / 2` in
  each physical copy of the zero head cell; and
* the structured prebridge ledger transports the resulting integral row
  change and the exact head-prime moments.

The source selector is not postulated through a new interface.  It is the
canonical protected-plus-ambient selector, and its finite selector state is
read directly from the existing
`BankPaperCanonicalRoundedSelectorTangentInput`.  Consequently the only
new feasibility work is at the two coordinates that actually change.

The terminal eventual theorem uses the same `hcanonical` and
`cellMassMargin` arguments as the canonical Proposition 8.7 statement.  It
only assumes that the ledger and rough guard agree on the positive, smooth,
at-most-`2n` structured universe.  Together with the canonical sample guards,
this yields pointwise exclusion from the full rough guard without any global
Finset equality.  To invoke the existing actual P87 endpoint consumer after
the structured placement, one must additionally identify
the rebalanced seed with a bridge baseline (`Hmeasure` and `hseed`) and
supply the existing analytic `Hfit`; those are retained under their
existing names rather than hidden in a new assumption package.
-/

open Filter Topology Asymptotics Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A reusable two-cell scalar capacity lemma -/



/-! ## Height-only capacity from the Section 8 ledger -/









/-! ## Reusing the rounded source selector -/







/-! ## Exact quota transport -/











/-! ## Canonical P87-local one-shot orchestration -/

/-- A fixed multiple of the upper-tail length is eventually at most the
ambient sample size. -/
theorem eventually_mul_upperTailLength_le_self
    (K : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      K * upperTailLength c n <= n := by
  have hT : Tendsto
      (fun n : Nat => (K : Real) *
        ((upperTailLength c n : Real) / (n : Real)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (upperTailLength_ratio_tendsto_zero hc).const_mul (K : Real)
  have hsmall := hT.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnPos
  have hn' :
      (K : Real) *
          ((upperTailLength c n : Real) / (n : Real)) < 1 := hn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hnPos
  have hnDiv :
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) < 1 := by
    calc
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) =
          (K : Real) *
            ((upperTailLength c n : Real) / (n : Real)) := by ring
      _ < 1 := hn'
  have hcross :
      (K : Real) * (upperTailLength c n : Real) < (n : Real) := by
    simpa only [one_mul] using (div_lt_iff₀ hnReal).mp hnDiv
  have hcast :
      ((K * upperTailLength c n : Nat) : Real) < (n : Real) := by
    push_cast
    exact hcross
  exact_mod_cast hcast.le







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

/-- The raw label-one head-free broad pool is not merely equinumerous with
a structured cell: it is literally the moving-upper structured cell for
the zero head pattern. -/
theorem bankPaperCanonicalRawSmoothBasePool_eq_zeroHeadStructuredCell
    (W n h K : Nat) :
    bankPaperCanonicalRawSmoothBasePool W n h K =
      structuredCell (roughHeadZeroPattern W)
        n (2 * n - K * h) (yNat n) := by
  classical
  ext a
  constructor
  · intro ha
    have haData : a ∈
        roughCanonicalBroadCorrectionPool
          W n h K (yNat n) 1 := by
      simpa only [bankPaperCanonicalRawSmoothBasePool] using ha
    have haRow := mem_completeRoughRowFiber.mp haData
    have haHead := mem_roughHeadFree.mp haRow.1
    have haBroad : n < a ∧ a <= 2 * n - K * h := by
      simpa only [roughBroadLowerBlock, Finset.mem_Ioc] using haHead.1
    have haPos : 0 < a := by omega
    apply mem_structuredCell.mpr
    refine
      ⟨mem_smoothInterval.mpr
          ⟨haBroad.1, haBroad.2,
            (completeRoughLabel_eq_one_iff_mem_smoothNumbers
              haPos).mp haRow.2⟩,
        ?_⟩
    apply
      ((roughHeadZeroPattern W).matches_iff_factor_dvd_and_coprime
        haPos.ne').mpr
    simpa only [roughHeadZeroPattern_factor, one_dvd, Nat.div_one,
      roughHeadZeroPattern_modulus, true_and] using haHead.2
  · intro ha
    have haCell := mem_structuredCell.mp ha
    have haInterval := mem_smoothInterval.mp haCell.1
    have haPos := pos_of_mem_smoothInterval haCell.1
    have haMatch :=
      ((roughHeadZeroPattern W).matches_iff_factor_dvd_and_coprime
        haPos.ne').mp haCell.2
    have haCoprime : Nat.Coprime a (roughHeadModulus W) := by
      simpa only [roughHeadZeroPattern_factor, one_dvd, Nat.div_one,
        roughHeadZeroPattern_modulus, true_and] using haMatch
    unfold bankPaperCanonicalRawSmoothBasePool
    unfold roughCanonicalBroadCorrectionPool
    apply mem_completeRoughRowFiber.mpr
    refine
      ⟨mem_roughHeadFree.mpr
          ⟨by
            simpa only [roughBroadLowerBlock, Finset.mem_Ioc] using
              ⟨haInterval.1, haInterval.2.1⟩,
            haCoprime⟩,
        (completeRoughLabel_eq_one_iff_mem_smoothNumbers
          haPos).mpr haInterval.2.2⟩



/-! ## Exact guarded-mass synchronization -/



/-! ## The three literal valuation moments -/









/-! ## Exact label-one source decomposition -/







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















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureBroad -/
section


/-!
# Canonical label-one broad-pool specialization

This file specializes the positive moving-prefix theorem to the literal
head-free smooth base pool and then transports the result through the
canonical numerical-guard deletion.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PaperMovingPrefixMarkedCell
open Erdos390.Full.PaperValuationCutoff
open Erdos390.Full.ValuationCutoff

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

private theorem sharp_physicalBound_one (n : Nat) :
    physicalBound (1 : Real) n = n := by
  unfold physicalBound
  norm_num

private theorem sharp_physicalBound_two (n : Nat) :
    physicalBound (2 : Real) n = 2 * n := by
  unfold physicalBound
  have hcast :
      (2 : Real) * (n : Real) = ((2 * n : Nat) : Real) := by
    norm_num
  rw [hcast, Nat.floor_natCast]

private theorem half_le_prefixFraction_one_two_of_two_mul_le
    {n t : Nat} (hn : 0 < n) (ht : 2 * t ≤ n) :
    (1 : Real) / 2 ≤
      prefixFraction 1 2 n (2 * n - t) := by
  have htUpper : t ≤ 2 * n := by omega
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have htR : 2 * (t : Real) ≤ (n : Real) := by exact_mod_cast ht
  unfold prefixFraction prefixScale
  rw [Nat.cast_sub htUpper, Nat.cast_mul]
  norm_num
  field_simp [hnR.ne']
  nlinarith

/-- A fixed multiple of the canonical upper-tail length is eventually small
enough that the moving label-one pool occupies at least half of `[n,2n]`. -/
private theorem eventually_two_mul_mul_upperTailLength_le_self
    (K : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      2 * (K * upperTailLength c n) ≤ n := by
  have hraw :=
    eventually_mul_upperTailLength_le_self (2 * K) hc
  filter_upwards [hraw] with n hn
  simpa only [Nat.mul_assoc] using hn

/-! ## Raw canonical broad pool -/

/-- The raw label-one head-free broad pool inherits the common sharp
full-valuation profile from the moving-prefix theorem. -/
theorem
    exists_uniform_rawSmoothBasePool_valuation_mean_profile_paperRate
    (W K : Nat) (hW : 1 < W) {c : Real} (hc : 0 < c) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {n p : Nat}, N₀ ≤ n → p ∈ primeBand n W →
        let S := bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K
        let Kcut := Nat.log p (yNat n ^ 4)
        ∃ hS : S.Nonempty,
          |(uniformOnFinset S hS).expect
                (fun m ↦ valuation p (m : Nat)) -
            ∑ j ∈ positiveExponents Kcut,
              paperDivisibilityMain n (p ^ j)| ≤
            Cval / ((p : Real) * L n) := by
  have hHeadLe :
      ∀ q ∈ (roughHeadZeroPattern W).primes, q ≤ W := by
    intro q hq
    change q ∈ primesUpTo W at hq
    exact (mem_primesUpTo.mp hq).2
  obtain ⟨Cval, hCval, Nraw, hraw⟩ :=
    exists_uniform_movingPrefix_valuation_mean_profile_paperRate_of_fraction
      (roughHeadZeroPattern W)
      (A := 1) (C := 2) (rmin := (1 : Real) / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      W hW hHeadLe
  have htail :=
    eventually_two_mul_mul_upperTailLength_le_self K hc
  have hgood : ∀ᶠ n : Nat in atTop,
      2 * (K * upperTailLength c n) ≤ n ∧ 1 < n := by
    filter_upwards [htail, Filter.eventually_gt_atTop 1]
      with n hsmall hn
    exact ⟨hsmall, hn⟩
  obtain ⟨Ntail, hNtail⟩ := Filter.eventually_atTop.mp hgood
  refine ⟨Cval, hCval, max Nraw Ntail, ?_⟩
  intro n p hN hpBand
  dsimp only
  have hNraw : Nraw ≤ n := by omega
  have hNtailBound : Ntail ≤ n := by omega
  obtain ⟨hsmall, hn⟩ := hNtail n hNtailBound
  let h := upperTailLength c n
  let t := K * h
  let k := 2 * n - t
  have hnpos : 0 < n := by omega
  have ht : 2 * t ≤ n := by simpa only [t, h] using hsmall
  have htTwo : t ≤ 2 * n := by omega
  have hlow : physicalBound (1 : Real) n < k := by
    rw [sharp_physicalBound_one]
    dsimp only [k]
    omega
  have hhigh : k ≤ physicalBound (2 : Real) n := by
    rw [sharp_physicalBound_two]
    dsimp only [k]
    omega
  have hfrac :
      (1 : Real) / 2 ≤ prefixFraction 1 2 n k := by
    dsimp only [k]
    exact half_le_prefixFraction_one_two_of_two_mul_le hnpos ht
  obtain ⟨hS, hbound⟩ :=
    hraw (n := n) (k := k) (p := p)
      hNraw hlow hhigh hfrac hpBand
  have hpool :
      bankPaperCanonicalRawSmoothBasePool W n h K =
        structuredCell (roughHeadZeroPattern W) n k (yNat n) := by
    simpa only [h, k, t] using
      bankPaperCanonicalRawSmoothBasePool_eq_zeroHeadStructuredCell
        W n h K
  have hpool' :
      bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K =
        structuredCell (roughHeadZeroPattern W)
          (physicalBound (1 : Real) n) k (yNat n) := by
    simpa only [h, sharp_physicalBound_one] using hpool
  let hPool :
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).Nonempty :=
    hpool'.symm ▸ hS
  refine ⟨hPool, ?_⟩
  have hreindex :
      (uniformOnFinset
          (structuredCell (roughHeadZeroPattern W)
            (physicalBound (1 : Real) n) k (yNat n)) hS).expect
            (fun m ↦ valuation p (m : Nat)) =
        (uniformOnFinset
          (bankPaperCanonicalRawSmoothBasePool W n
            (upperTailLength c n) K) hPool).expect
            (fun m ↦ valuation p (m : Nat)) := by
    have htilt :=
      uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq
        (structuredCell (roughHeadZeroPattern W)
          (physicalBound (1 : Real) n) k (yNat n))
        (bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K)
        hpool'.symm hS hPool
        (fun _ ↦ (0 : Real)) (fun _ ↦ (0 : Real))
        (by
          intro x y hxy
          rfl)
        (fun m : Nat ↦ valuation p m)
    simpa only [finiteProbability_exponentialTilt_zero_expect] using htilt
  rw [← hreindex]
  exact hbound

/-! ## Canonical guard deletion -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal007_010 := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_uniform_rawSmoothBasePool_valuation_mean_profile_paperRate
