-- Prove2me | solution 1 for Erdos390.WholePaper.exists_eventually_bankOrdinary_markerCount_lower
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:22:32.936456+00:00
-- url     : https://prove2.me/submissions/0eb583fd-530a-4a35-914b-f0601fdfa07e

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Theorems.Thm_Erdos390_WholePaper_exists_eventually_bankOrdinarySmoothBulkDonors_lower

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/

















theorem primeLogSumInterval_eq_sub {z y : ℕ} (hzy : z ≤ y) :
    primeLogSumInterval z y = primeLogSumUpTo y - primeLogSumUpTo z := by
  have hsubset : (z + 1).primesBelow ⊆ (y + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum := Finset.sum_sdiff
    (f := fun p : ℕ => Real.log (p : ℝ)) hsubset
  simp only [primeLogSumInterval, primeLogSumUpTo] at hsum ⊢
  linarith

/-- Uniform two-endpoint form of the quantitative PNT.  This is the exact
finite interval estimate used on each cell of a prime Stieltjes partition. -/
theorem primeLogSumInterval_error_bound {A C : ℝ} {X₀ z y : ℕ}
    (hbound : ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / (Real.log (X : ℝ)) ^ A))
    (hz : X₀ ≤ z) (hy : X₀ ≤ y) (hzy : z ≤ y) :
    |primeLogSumInterval z y - ((y : ℝ) - (z : ℝ))| ≤
      C * ((y : ℝ) / (Real.log (y : ℝ)) ^ A +
        (z : ℝ) / (Real.log (z : ℝ)) ^ A) := by
  rw [primeLogSumInterval_eq_sub hzy]
  calc
    |(primeLogSumUpTo y - primeLogSumUpTo z) - ((y : ℝ) - (z : ℝ))| =
        |(primeLogSumUpTo y - (y : ℝ)) -
          (primeLogSumUpTo z - (z : ℝ))| := by ring_nf
    _ ≤ |primeLogSumUpTo y - (y : ℝ)| +
        |primeLogSumUpTo z - (z : ℝ)| := abs_sub _ _
    _ ≤ C * ((y : ℝ) / (Real.log (y : ℝ)) ^ A) +
        C * ((z : ℝ) / (Real.log (z : ℝ)) ^ A) :=
      add_le_add (hbound y hy) (hbound z hz)
    _ = _ := by ring































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/



















































/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/





























































end Erdos390.Full.FriableAsymptotic

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



/-- Every upper endpoint lies weakly above `2n`. -/
theorem two_mul_le_upperEndpoint (n h : ℕ) :
    2 * n ≤ upperEndpoint n h := by
  simp only [upperEndpoint, Nat.le_add_right]

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankMarkerDonorCombinatorics -/
section


/-!
# Finite marker--donor combinatorics

This file treats eligibility as an actual finite relation of marker--donor
pairs.  It proves only finite double counting, bounded-multiplicity counting,
choice of one donor already present in the relation, and a balanced split of
the chosen pairs into two orientation pools.  It makes no prime-number-theorem
or asymptotic supply assertion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section









/-- Literal double count of the finite marker--donor relation by marker fibers. -/
theorem sum_bankDonorMultiplicity_eq_occurrenceTotal
    {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) :
    ∑ marker ∈ bankEligibleMarkers eligible,
        bankDonorMultiplicity eligible marker =
      bankMarkerOccurrenceTotal eligible := by
  unfold bankEligibleMarkers bankDonorMultiplicity bankMarkerOccurrenceTotal
  exact (Finset.card_eq_sum_card_image Prod.fst eligible).symm

/-- A uniform fiber bound gives the literal occurrence bound `C ≤ m * K`. -/
theorem bankMarkerOccurrenceTotal_le_mul_markerCount
    {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) (m : ℕ)
    (hmultiplicity : ∀ marker ∈ bankEligibleMarkers eligible,
      bankDonorMultiplicity eligible marker ≤ m) :
    bankMarkerOccurrenceTotal eligible ≤
      m * bankEligibleMarkerCount eligible := by
  rw [← sum_bankDonorMultiplicity_eq_occurrenceTotal eligible]
  unfold bankEligibleMarkerCount
  calc
    (∑ marker ∈ bankEligibleMarkers eligible,
        bankDonorMultiplicity eligible marker) ≤
        ∑ _marker ∈ bankEligibleMarkers eligible, m := by
      exact Finset.sum_le_sum fun marker hmarker ↦
        hmultiplicity marker hmarker
    _ = m * (bankEligibleMarkers eligible).card := by
      simp [mul_comm]















































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryDonorRelation -/
section


/-!
# The ordinary-bank marker--donor relation

This file defines the literal finite relation used by the nonbottom bank in
Section 5.3.  The scale is rational, so the grid `Q_j = 4(4/3)^j` and all four
interval endpoints are represented without rounding.  The wider relation is
the actual relation from which marker--donor pairs are selected.  The narrow
relation is the bulk subrelation used in the analytic supply proof.

There is no prime-distribution input here.  In particular, the fiber bound is
an exact injection into the natural quotient interval
`(2n / P, M / P]`.  The five fixed small-scale donors are also recorded here,
including their literal rational interval checks.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section













theorem ordinaryBankBulkDonorWindow_subset
    {Q : ℚ} {u : ℕ} (hu : InOrdinaryBankBulkDonorWindow Q u) :
    InOrdinaryBankDonorWindow Q u := by
  unfold InOrdinaryBankBulkDonorWindow at hu
  unfold InOrdinaryBankDonorWindow
  constructor <;> linarith

















/-- The constants `7/5` and `29/20` put every bulk tail occurrence in the
actual marker interval as soon as the upper endpoint is at most `2.1n`. -/
theorem ordinaryBankBulkPair_isEligible
    {n M : ℕ} {Q : ℚ} {pair : ℕ × ℕ}
    (hM : 10 * M ≤ 21 * n)
    (hpair : IsOrdinaryBankBulkPair n M Q pair) :
    IsOrdinaryBankEligiblePair n M Q pair := by
  rcases pair with ⟨P, u⟩
  rcases hpair with ⟨hQ, hP, hu, huBulk, huSmooth, htailLower,
    htailUpper⟩
  have hPnonneg : (0 : ℚ) ≤ P := by positivity
  have huBulkPLeft := mul_le_mul_of_nonneg_right huBulk.1 hPnonneg
  have huBulkPRight := mul_le_mul_of_nonneg_right huBulk.2 hPnonneg
  have htailLowerQ : 2 * (n : ℚ) < (P : ℚ) * (u : ℚ) := by
    exact_mod_cast htailLower
  have htailUpperQ : (P : ℚ) * (u : ℚ) ≤ M := by
    exact_mod_cast htailUpper
  have hMQ : 10 * (M : ℚ) ≤ 21 * (n : ℚ) := by
    exact_mod_cast hM
  have hmarker : InOrdinaryBankMarkerInterval n Q P := by
    unfold InOrdinaryBankMarkerInterval
    constructor <;> nlinarith
  exact ⟨hQ, hP, hu, hmarker,
    ordinaryBankBulkDonorWindow_subset huBulk, huSmooth,
    htailLower, htailUpper⟩

/-- Hence the bulk finite relation is literally a subrelation of the actual
one in the endpoint range used by the paper. -/
theorem bankOrdinaryBulkRelation_subset_eligible
    {n M : ℕ} {Q : ℚ} (hM : 10 * M ≤ 21 * n) :
    bankOrdinaryBulkRelation n M Q ⊆
      bankOrdinaryEligibleRelation n M Q := by
  intro pair hpair
  rw [mem_bankOrdinaryEligibleRelation]
  exact ordinaryBankBulkPair_isEligible hM
    (mem_bankOrdinaryBulkRelation.mp hpair)

/-- Exact marker-fiber bound: admissible donors inject into the quotient
interval `(2n/P, M/P]`. -/
theorem bankOrdinary_donorMultiplicity_le_div_sub_div
    {n M P : ℕ} {Q : ℚ} (hP : 0 < P) :
    bankDonorMultiplicity (bankOrdinaryEligibleRelation n M Q) P ≤
      M / P - (2 * n) / P := by
  unfold bankDonorMultiplicity
  have hmap : Set.MapsTo Prod.snd
      (↑((bankOrdinaryEligibleRelation n M Q).filter
        fun pair ↦ pair.1 = P) : Set (ℕ × ℕ))
      (↑(Finset.Ioc ((2 * n) / P) (M / P)) : Set ℕ) := by
    intro pair hpair
    have hfilter := Finset.mem_filter.mp hpair
    have heligible := mem_bankOrdinaryEligibleRelation.mp hfilter.1
    have hfirst : pair.1 = P := hfilter.2
    change pair.2 ∈ Finset.Ioc ((2 * n) / P) (M / P)
    rw [Finset.mem_Ioc]
    constructor
    · apply (Nat.div_lt_iff_lt_mul hP).2
      simpa only [hfirst, Nat.mul_comm] using heligible.2.2.2.2.2.2.1
    · apply (Nat.le_div_iff_mul_le hP).2
      simpa only [hfirst, Nat.mul_comm] using heligible.2.2.2.2.2.2.2
  have hinj : Set.InjOn Prod.snd
      (↑((bankOrdinaryEligibleRelation n M Q).filter
        fun pair ↦ pair.1 = P) : Set (ℕ × ℕ)) := by
    intro pair hpair pair' hpair' hsnd
    have hp := (Finset.mem_filter.mp hpair).2
    have hp' := (Finset.mem_filter.mp hpair').2
    apply Prod.ext
    · exact hp.trans hp'.symm
    · exact hsnd
  have hcard := Finset.card_le_card_of_injOn Prod.snd hmap hinj
  simpa only [Nat.card_Ioc] using hcard

/-! ## The five exceptional fixed donors -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryDonorSupply -/
section


/-!
# Analytic supply for the ordinary bank

This file supplies the analytic half of the ordinary marker--donor argument.
The only prime-number input is the already audited cumulative estimate
`FriableAsymptotic.exists_primeLogSumUpTo_error_bound 3`.  We first turn its
two endpoint errors into a lower bound for an actual finite prime interval.
We then count the literal smooth donor window, sum the resulting occurrences,
and pass the exact marker-fiber bound through
`bankOccurrenceCeilDiv_le_markerCount`.

No asymptotic assertion is stored in a structure or accepted as a field.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.FriableAsymptotic

noncomputable section

/-! ## A cumulative-theta short-interval lemma -/



private theorem bankPrimeInterval_eq_logSumSupport (A B : ℕ) :
    bankPrimeInterval A B =
      (B + 1).primesBelow \ (A + 1).primesBelow := by
  ext p
  by_cases hp : p.Prime
  · simp only [bankPrimeInterval, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, Nat.mem_primesBelow, hp, and_true]
    omega
  · simp [bankPrimeInterval, Nat.mem_primesBelow, hp]

private theorem primeLogSumInterval_le_card_mul_log
    {A B : ℕ} :
    primeLogSumInterval A B ≤
      (bankPrimeInterval A B).card * Real.log (B : ℝ) := by
  rw [primeLogSumInterval, ← bankPrimeInterval_eq_logSumSupport]
  calc
    ∑ p ∈ bankPrimeInterval A B, Real.log (p : ℝ) ≤
        ∑ _p ∈ bankPrimeInterval A B, Real.log (B : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpmem := (Finset.mem_filter.mp hp)
      have hpIoc := Finset.mem_Ioc.mp hpmem.1
      exact Real.log_le_log (by exact_mod_cast hpmem.2.pos)
        (by exact_mod_cast hpIoc.2)
    _ = (bankPrimeInterval A B).card * Real.log (B : ℝ) := by
      simp

/-- A direct consequence of a two-endpoint cumulative theta error.  This is
the precise mechanism used below: no theorem about arbitrary short intervals
is imported or assumed. -/
theorem primeInterval_card_lower_of_logSum_error
    {C : ℝ} {X₀ A B : ℕ}
    (hC : 0 ≤ C)
    (hX₀ : 2 ≤ X₀)
    (herror : ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / Real.log (X : ℝ) ^ (3 : ℕ)))
    (hA : X₀ ≤ A) (hAB : A ≤ B)
    (hdominates :
      2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
        (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
          (B : ℝ) - (A : ℝ)) :
    ((B : ℝ) - (A : ℝ)) / (2 * Real.log (B : ℝ)) ≤
      (bankPrimeInterval A B).card := by
  have hA2 : 2 ≤ A := hX₀.trans hA
  have hB2 : 2 ≤ B := hA2.trans hAB
  have herrorR : ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / Real.log (X : ℝ) ^ (3 : ℝ)) := by
    intro X hX
    simpa [Real.rpow_natCast] using herror X hX
  have hinterval := primeLogSumInterval_error_bound herrorR hA
    (hA.trans hAB) hAB
  have hintervalNat :
      |primeLogSumInterval A B - ((B : ℝ) - (A : ℝ))| ≤
        C * ((B : ℝ) / Real.log (B : ℝ) ^ (3 : ℕ) +
          (A : ℝ) / Real.log (A : ℝ) ^ (3 : ℕ)) := by
    simpa [Real.rpow_natCast] using hinterval
  have hnonneg :
      0 ≤ C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
        (A : ℝ) / Real.log (A : ℝ) ^ 3) := by
    positivity
  have hlower :
      ((B : ℝ) - (A : ℝ)) / 2 ≤
        primeLogSumInterval A B := by
    have habsLower := neg_le_of_abs_le hintervalNat
    nlinarith
  have hsumUpper := primeLogSumInterval_le_card_mul_log (A := A) (B := B)
  have hlogB : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  apply (div_le_iff₀ (mul_pos (by norm_num) hlogB)).2
  have hhalf := hlower.trans hsumUpper
  nlinarith

/-- The preceding finite lemma with constants obtained directly from the
audited power-three theta estimate. -/
theorem exists_primeInterval_card_lower_from_cumulativePNT :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, 2 ≤ X₀ ∧
      ∀ A B : ℕ, X₀ ≤ A → A ≤ B →
        2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
          (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
            (B : ℝ) - (A : ℝ) →
        ((B : ℝ) - (A : ℝ)) /
            (2 * Real.log (B : ℝ)) ≤
          (bankPrimeInterval A B).card := by
  obtain ⟨C, hC, X₀, hX₀⟩ :=
    exists_primeLogSumUpTo_error_bound (3 : ℝ)
  let X₁ : ℕ := max X₀ 2
  have hX₁2 : 2 ≤ X₁ := le_max_right _ _
  have hbound : ∀ X, X₁ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / Real.log (X : ℝ) ^ (3 : ℕ)) := by
    intro X hX
    have hraw := hX₀ X ((le_max_left X₀ 2).trans hX)
    simpa [Real.rpow_natCast] using hraw
  exact ⟨C, hC, X₁, hX₁2, fun A B hA hAB hdom ↦
    primeInterval_card_lower_of_logSum_error hC.le hX₁2 hbound hA hAB hdom⟩

/-! ## The literal smooth donor window -/





















/-! ## Summing one-donor prime intervals -/





/-- The bulk occurrence relation contains the disjoint union of the prime
intervals supplied by every smooth donor in its literal window. -/
theorem sum_bankOrdinaryPrimeChoices_le_bulkRelation
    {n M : ℕ} {Q : ℚ} (hQ : 20 < Q) :
    ∑ u ∈ bankOrdinarySmoothBulkDonors n Q,
        (bankOrdinaryPrimeChoices n M u).card ≤
      (bankOrdinaryBulkRelation n M Q).card := by
  have hQpos : 0 < Q := by linarith
  have hQnonneg : 0 ≤ Q := hQpos.le
  have hmaps : Set.MapsTo Prod.snd
      (↑(bankOrdinaryBulkRelation n M Q) : Set (ℕ × ℕ))
      (↑(bankOrdinarySmoothBulkDonors n Q) : Set ℕ) := by
    intro pair hpair
    have hp := mem_bankOrdinaryBulkRelation.mp hpair
    exact (mem_bankOrdinarySmoothBulkDonors hQnonneg).mpr
      ⟨hp.2.2.2.1, hp.2.2.2.2.1⟩
  have hfiber : ∀ u ∈ bankOrdinarySmoothBulkDonors n Q,
      (bankOrdinaryPrimeChoices n M u).card ≤
        ((bankOrdinaryBulkRelation n M Q).filter
          fun pair ↦ pair.2 = u).card := by
    intro u hu
    have huData := (mem_bankOrdinarySmoothBulkDonors hQnonneg).mp hu
    have huPos : 0 < u := by
      have huQ : (0 : ℚ) < u := by nlinarith [huData.1.1]
      exact_mod_cast huQ
    apply Finset.card_le_card_of_injOn (fun P : ℕ ↦ (P, u))
    · intro P hP
      have hPData := (mem_bankOrdinaryPrimeChoices huPos).mp hP
      apply Finset.mem_filter.mpr
      constructor
      · rw [mem_bankOrdinaryBulkRelation]
        exact ⟨hQpos, hPData.1, huPos, huData.1, huData.2,
          hPData.2.1, hPData.2.2⟩
      · rfl
    · intro P _ P' _ hpair
      exact congrArg Prod.fst hpair
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  rw [hpartition]
  exact Finset.sum_le_sum fun u hu ↦ hfiber u hu

/-- The actual relation has at least the summed bulk occurrences whenever the
paper's endpoint is at most `2.1n`. -/
theorem sum_bankOrdinaryPrimeChoices_le_occurrenceTotal
    {n M : ℕ} {Q : ℚ} (hQ : 20 < Q)
    (hM : 10 * M ≤ 21 * n) :
    ∑ u ∈ bankOrdinarySmoothBulkDonors n Q,
        (bankOrdinaryPrimeChoices n M u).card ≤
      bankMarkerOccurrenceTotal (bankOrdinaryEligibleRelation n M Q) := by
  exact (sum_bankOrdinaryPrimeChoices_le_bulkRelation hQ).trans
    (Finset.card_le_card
      (bankOrdinaryBulkRelation_subset_eligible hM))

/-! ## Uniform one-donor geometry -/

private theorem cast_natDiv_le_realDiv (x q : ℕ) :
    ((x / q : ℕ) : ℝ) ≤ (x : ℝ) / (q : ℝ) :=
  Nat.cast_div_le

private theorem realDiv_sub_one_lt_cast_natDiv
    (x q : ℕ) (_hq : 0 < q) :
    (x : ℝ) / (q : ℝ) - 1 < ((x / q : ℕ) : ℝ) := by
  have hfloor :
      (x : ℝ) / (q : ℝ) < ((x / q : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using
      (Nat.lt_floor_add_one ((x : ℝ) / (q : ℝ)))
  linarith

private theorem sevenNinthPower_div_log_tendsto_atTop :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) ^ (7 / 9 : ℝ) / Real.log (n : ℝ))
      atTop atTop := by
  have hzeroReal : Tendsto
      (fun x : ℝ ↦ Real.log x / x ^ (7 / 9 : ℝ))
      atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
        (by norm_num : (0 : ℝ) < 7 / 9)).tendsto_div_nhds_zero
  have hzero : Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) /
        (n : ℝ) ^ (7 / 9 : ℝ))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, Real.rpow_one] using
      hzeroReal.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (n : ℝ) / (n : ℝ) ^ (7 / 9 : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (by positivity)
  have hright : Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) /
        (n : ℝ) ^ (7 / 9 : ℝ))
      atTop (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦ by
    simp only [Pi.inv_apply, inv_div]

private theorem eventually_log_sq_ge (D : ℝ) :
    ∀ᶠ n : ℕ in atTop, D ≤ Real.log (n : ℝ) ^ 2 := by
  let r : ℝ := Real.sqrt (max D 0)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hlog : ∀ᶠ n : ℕ in atTop, r ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop r)
  filter_upwards [hlog] with n hn
  have hsqrt : r ^ 2 = max D 0 := by
    exact Real.sq_sqrt (le_max_right D 0)
  have hD : D ≤ r ^ 2 := by rw [hsqrt]; exact le_max_left _ _
  nlinarith

set_option maxHeartbeats 800000 in
private theorem eventually_bankOrdinary_oneDonor_geometry
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C) (X₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      10 * upperTailLength c n ≤ n ∧
      (upperTailLength c n : ℝ) ≤
        2 * c * secondOrderScale n ∧
      ∀ Q : ℚ, 20 < Q → Q ≤ (yNat n : ℚ) →
        ∀ u : ℕ, InOrdinaryBankBulkDonorWindow Q u →
          let A := (2 * n) / u
          let B := upperEndpoint n (upperTailLength c n) / u
          X₀ ≤ A ∧ A ≤ B ∧
          c / 10 * (n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ)) ≤
            (B : ℝ) - (A : ℝ) ∧
          (7 / 9 : ℝ) * Real.log (n : ℝ) ≤
            Real.log (A : ℝ) ∧
          Real.log (B : ℝ) ≤ 2 * Real.log (n : ℝ) ∧
          (B : ℝ) ≤
            3 / 2 * (n : ℝ) / (Q : ℝ) ∧
          2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
            (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
              (B : ℝ) - (A : ℝ) := by
  have htailLower : ∀ᶠ n : ℕ in atTop,
      c / 2 ≤ (upperTailLength c n : ℝ) / secondOrderScale n :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_ge_nhds (half_lt_self hc))
  have htailUpper : ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) / secondOrderScale n ≤ 2 * c :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_le_nhds (by linarith : c < 2 * c))
  have htailSmall : ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) / (n : ℝ) < 1 / 10 :=
    (upperTailLength_ratio_tendsto_zero hc).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 10))
  have hzTop : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (7 / 9 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 9)).comp
      tendsto_natCast_atTop_atTop
  have hzLarge : ∀ᶠ n : ℕ in atTop,
      (max X₀ 3 : ℝ) ≤ (n : ℝ) ^ (7 / 9 : ℝ) :=
    hzTop.eventually (eventually_ge_atTop (max X₀ 3 : ℝ))
  have hratioLarge : ∀ᶠ n : ℕ in atTop,
      1 ≤ (71 * c / 290) *
        ((n : ℝ) ^ (7 / 9 : ℝ) / Real.log (n : ℝ)) := by
    have ht := (sevenNinthPower_div_log_tendsto_atTop.const_mul_atTop
      (by positivity : 0 < 71 * c / 290)).eventually
        (eventually_ge_atTop (1 : ℝ))
    simpa only [mul_div_assoc] using ht
  have herrorLarge : ∀ᶠ n : ℕ in atTop,
      60 * C ≤ c * (7 / 9 : ℝ) ^ 3 * Real.log (n : ℝ) ^ 2 := by
    have hsq := eventually_log_sq_ge
      (60 * C / (c * (7 / 9 : ℝ) ^ 3))
    filter_upwards [hsq] with n hn
    have hcoef : 0 < c * (7 / 9 : ℝ) ^ 3 := by positivity
    have hh := (div_le_iff₀ hcoef).mp (by simpa only using hn)
    calc
      60 * C ≤ Real.log (n : ℝ) ^ 2 *
          (c * (7 / 9 : ℝ) ^ 3) := hh
      _ = c * (7 / 9 : ℝ) ^ 3 * Real.log (n : ℝ) ^ 2 :=
        mul_comm _ _
  filter_upwards [eventually_gt_atTop 3, eventually_secondOrderScale_pos,
      htailLower, htailUpper, htailSmall, hzLarge, hratioLarge,
      herrorLarge] with n hn hscale htailLo htailHi htailRatio hz
        hratio herror
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have htailNat : 10 * upperTailLength c n ≤ n := by
    have hmul : (upperTailLength c n : ℝ) <
        (1 / 10 : ℝ) * (n : ℝ) :=
      (div_lt_iff₀ hnR).mp htailRatio
    have hmulLe : (10 : ℝ) * upperTailLength c n ≤ (n : ℝ) := by
      nlinarith
    exact_mod_cast hmulLe
  have htailCastUpper : (upperTailLength c n : ℝ) ≤
      2 * c * secondOrderScale n := by
    exact (div_le_iff₀ hscale).mp htailHi
  refine ⟨htailNat, htailCastUpper, ?_⟩
  intro Q hQ hQY u hu
  dsimp only
  have hQposRat : (0 : ℚ) < Q := by linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQposRat
  have huRatPos : (0 : ℚ) < u := by nlinarith [hu.1]
  have huPos : 0 < u := by exact_mod_cast huRatPos
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast huPos
  have huLower : 7 * (Q : ℝ) ≤ 5 * (u : ℝ) := by
    exact_mod_cast hu.1
  have huUpper : 20 * (u : ℝ) ≤ 29 * (Q : ℝ) := by
    exact_mod_cast hu.2
  have hQYreal : (Q : ℝ) ≤ (yNat n : ℝ) := by
    exact_mod_cast hQY
  have hyNat : (yNat n : ℝ) ≤
      (n : ℝ) ^ (2 / 9 : ℝ) := by
    exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hQpow : (Q : ℝ) ≤ (n : ℝ) ^ (2 / 9 : ℝ) :=
    hQYreal.trans hyNat
  let z : ℝ := (n : ℝ) ^ (7 / 9 : ℝ)
  have hzPos : 0 < z := by dsimp only [z]; positivity
  have hpowProduct : (n : ℝ) ^ (2 / 9 : ℝ) * z = (n : ℝ) := by
    dsimp only [z]
    rw [← Real.rpow_add hnR]
    norm_num [Real.rpow_one]
  have hzQ : z ≤ (n : ℝ) / (Q : ℝ) := by
    apply (le_div_iff₀ hQpos).2
    calc
      z * (Q : ℝ) ≤ z * (n : ℝ) ^ (2 / 9 : ℝ) := by gcongr
      _ = (n : ℝ) := by rw [mul_comm, hpowProduct]
  have hzThree : 3 ≤ z := by
    exact le_trans (by exact_mod_cast (le_max_right X₀ 3)) hz
  let A : ℕ := (2 * n) / u
  let B : ℕ := upperEndpoint n (upperTailLength c n) / u
  have hAleReal : z ≤ (A : ℝ) := by
    have hdivLower := realDiv_sub_one_lt_cast_natDiv (2 * n) u huPos
    have hmain : 40 / 29 * z ≤
        (2 * (n : ℝ)) / (u : ℝ) := by
      apply (le_div_iff₀ huR).2
      have hnQ : z * (Q : ℝ) ≤ (n : ℝ) :=
        (le_div_iff₀ hQpos).mp hzQ
      nlinarith [huUpper]
    dsimp only [A]
    push_cast at hdivLower
    nlinarith
  have hX₀A : X₀ ≤ A := by
    have hXmax : (X₀ : ℝ) ≤ (max X₀ 3 : ℝ) := by
      exact_mod_cast (le_max_left X₀ 3)
    have hXz : (X₀ : ℝ) ≤ z := hXmax.trans hz
    have hXreal : (X₀ : ℝ) ≤ (A : ℝ) := hXz.trans hAleReal
    exact_mod_cast hXreal
  have hAB : A ≤ B := by
    dsimp only [A, B]
    exact Nat.div_le_div_right (two_mul_le_upperEndpoint n
      (upperTailLength c n))
  have hBLower := realDiv_sub_one_lt_cast_natDiv
    (upperEndpoint n (upperTailLength c n)) u huPos
  have hAUpper := cast_natDiv_le_realDiv (2 * n) u
  have htailLowerCast : c / 2 * secondOrderScale n ≤
      (upperTailLength c n : ℝ) := by
    exact (le_div_iff₀ hscale).mp htailLo
  have hwidth : c / 10 * (n : ℝ) /
        ((Q : ℝ) * Real.log (n : ℝ)) ≤
      (B : ℝ) - (A : ℝ) := by
    have hscaleEq : secondOrderScale n =
        (n : ℝ) / Real.log (n : ℝ) := rfl
    have htailDiv :
        10 * c / 29 * ((n : ℝ) /
          ((Q : ℝ) * Real.log (n : ℝ))) ≤
          (upperTailLength c n : ℝ) / (u : ℝ) := by
      apply (le_div_iff₀ huR).2
      calc
        (10 * c / 29 * ((n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ)))) * (u : ℝ) =
            (c / 2 * ((n : ℝ) / Real.log (n : ℝ))) *
              (20 * (u : ℝ) / (29 * (Q : ℝ))) := by
                field_simp [hQpos.ne', hlogN.ne']
                ring
        _ ≤ (c / 2 * ((n : ℝ) / Real.log (n : ℝ))) * 1 := by
          gcongr
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 29 * Q)).2
          nlinarith [huUpper]
        _ = c / 2 * secondOrderScale n := by
          rw [secondOrderScale]
          ring
        _ ≤ (upperTailLength c n : ℝ) := htailLowerCast
    have hratioUse :
        1 ≤ 71 * c / 290 *
          ((n : ℝ) / ((Q : ℝ) * Real.log (n : ℝ))) := by
      calc
        1 ≤ 71 * c / 290 * (z / Real.log (n : ℝ)) := hratio
        _ ≤ 71 * c / 290 *
            ((n : ℝ) / ((Q : ℝ) * Real.log (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            z / Real.log (n : ℝ) ≤
                ((n : ℝ) / (Q : ℝ)) / Real.log (n : ℝ) :=
              div_le_div_of_nonneg_right hzQ hlogN.le
            _ = (n : ℝ) / ((Q : ℝ) * Real.log (n : ℝ)) := by
              field_simp [hQpos.ne', hlogN.ne']
    dsimp only [A, B] at hBLower hAUpper ⊢
    rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hBLower
    push_cast at hBLower hAUpper
    have hfloorGap : (upperTailLength c n : ℝ) / (u : ℝ) - 1 ≤
        ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ) := by
      calc
        (upperTailLength c n : ℝ) / (u : ℝ) - 1 =
            ((2 * (n : ℝ) + upperTailLength c n) / (u : ℝ) - 1) -
              (2 * (n : ℝ)) / (u : ℝ) := by ring
        _ ≤ ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
              (((2 * n) / u : ℕ) : ℝ) := by
          apply sub_le_sub hBLower.le
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hAUpper
    calc
      c / 10 * (n : ℝ) / ((Q : ℝ) * Real.log (n : ℝ)) =
          10 * c / 29 * ((n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ))) -
            71 * c / 290 * ((n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ))) := by ring
      _ ≤ (upperTailLength c n : ℝ) / (u : ℝ) - 1 :=
        sub_le_sub htailDiv hratioUse
      _ ≤ ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ) := hfloorGap
  have hlogA : (7 / 9 : ℝ) * Real.log (n : ℝ) ≤
      Real.log (A : ℝ) := by
    have hzLog : Real.log z =
        (7 / 9 : ℝ) * Real.log (n : ℝ) := by
      dsimp only [z]
      exact Real.log_rpow hnR (7 / 9 : ℝ)
    rw [← hzLog]
    exact Real.log_le_log hzPos hAleReal
  have hMcast : (upperEndpoint n (upperTailLength c n) : ℝ) ≤
      21 / 10 * (n : ℝ) := by
    rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have htailR : (upperTailLength c n : ℝ) ≤ (n : ℝ) / 10 := by
      have htailMul : (10 : ℝ) * upperTailLength c n ≤ (n : ℝ) := by
        exact_mod_cast htailNat
      nlinarith
    linarith
  have hBupper : (B : ℝ) ≤
      3 / 2 * (n : ℝ) / (Q : ℝ) := by
    have hdiv := cast_natDiv_le_realDiv
      (upperEndpoint n (upperTailLength c n)) u
    dsimp only [B]
    calc
      ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) ≤
          (upperEndpoint n (upperTailLength c n) : ℝ) / (u : ℝ) := hdiv
      _ ≤ (21 / 10 * (n : ℝ)) / (7 / 5 * (Q : ℝ)) := by
        exact div_le_div₀ (by positivity) hMcast
          (by positivity : (0 : ℝ) < 7 / 5 * Q) (by nlinarith [huLower])
      _ = 3 / 2 * (n : ℝ) / (Q : ℝ) := by
        field_simp [hQpos.ne']
        ring
  have hlogB : Real.log (B : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hAcast : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
    have hBpos : 0 < (B : ℝ) := hzPos.trans_le (hAleReal.trans hAcast)
    have hBthree : (B : ℝ) ≤ 3 * (n : ℝ) := by
      have hQtwenty : (20 : ℝ) < Q := by exact_mod_cast hQ
      calc
        (B : ℝ) ≤ 3 / 2 * (n : ℝ) / (Q : ℝ) := hBupper
        _ ≤ 3 * (n : ℝ) := by
          apply (div_le_iff₀ hQpos).2
          nlinarith
    calc
      Real.log (B : ℝ) ≤ Real.log (3 * (n : ℝ)) :=
        Real.log_le_log hBpos hBthree
      _ = Real.log 3 + Real.log (n : ℝ) := by
        rw [Real.log_mul (by norm_num) hnR.ne']
      _ ≤ 2 * Real.log (n : ℝ) := by
        have : Real.log 3 ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hn.le)
        linarith
  have herrorDom :
      2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
        (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
          (B : ℝ) - (A : ℝ) := by
    have hlogApos : 0 < Real.log (A : ℝ) :=
      (mul_pos (by norm_num : (0 : ℝ) < 7 / 9) hlogN).trans_le hlogA
    have hlogAle : Real.log (A : ℝ) ≤ Real.log (B : ℝ) := by
      exact Real.log_le_log (hzPos.trans_le hAleReal) (by exact_mod_cast hAB)
    have hAcast : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
    have hbaseLogPos : 0 < (7 / 9 : ℝ) * Real.log (n : ℝ) :=
      mul_pos (by norm_num) hlogN
    have hbaseLogA : (7 / 9 : ℝ) * Real.log (n : ℝ) ≤
        Real.log (A : ℝ) := hlogA
    have hbaseLogB : (7 / 9 : ℝ) * Real.log (n : ℝ) ≤
        Real.log (B : ℝ) := hbaseLogA.trans hlogAle
    have hsum :
        (B : ℝ) / Real.log (B : ℝ) ^ 3 +
          (A : ℝ) / Real.log (A : ℝ) ^ 3 ≤
        3 * (n : ℝ) /
          ((Q : ℝ) * ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3) := by
      have htermB : (B : ℝ) / Real.log (B : ℝ) ^ 3 ≤
          (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 := by
        exact div_le_div_of_nonneg_left (by positivity)
          (pow_pos hbaseLogPos 3)
          (pow_le_pow_left₀ hbaseLogPos.le hbaseLogB 3)
      have htermA : (A : ℝ) / Real.log (A : ℝ) ^ 3 ≤
          (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 := by
        calc
          (A : ℝ) / Real.log (A : ℝ) ^ 3 ≤
              (B : ℝ) / Real.log (A : ℝ) ^ 3 :=
            div_le_div_of_nonneg_right hAcast (by positivity)
          _ ≤ (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 :=
            div_le_div_of_nonneg_left (by positivity)
              (pow_pos hbaseLogPos 3)
              (pow_le_pow_left₀ hbaseLogPos.le hbaseLogA 3)
      calc
        _ ≤ (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 +
            (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 :=
          add_le_add htermB htermA
        _ = 2 * (B : ℝ) /
            ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 := by ring
        _ ≤ 3 * (n : ℝ) /
            ((Q : ℝ) * ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3) := by
          have hnum : 2 * (B : ℝ) ≤ 3 * (n : ℝ) / (Q : ℝ) := by
            calc
              2 * (B : ℝ) ≤ 2 * (3 / 2 * (n : ℝ) / (Q : ℝ)) :=
                mul_le_mul_of_nonneg_left hBupper (by norm_num)
              _ = 3 * (n : ℝ) / (Q : ℝ) := by ring
          calc
            2 * (B : ℝ) / ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 ≤
                (3 * (n : ℝ) / (Q : ℝ)) /
                  ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3 :=
              div_le_div_of_nonneg_right hnum (by positivity)
            _ = 3 * (n : ℝ) /
                ((Q : ℝ) * ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3) := by
              field_simp [hQpos.ne']
    calc
      2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
          (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
          2 * C * (3 * (n : ℝ) /
            ((Q : ℝ) * ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3)) := by
        gcongr
      _ ≤ c / 10 * (n : ℝ) /
          ((Q : ℝ) * Real.log (n : ℝ)) := by
        calc
          2 * C * (3 * (n : ℝ) /
              ((Q : ℝ) * ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3)) =
            (60 * C) * ((n : ℝ) /
              (10 * (Q : ℝ) *
                ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3)) := by ring
          _ ≤ (c * (7 / 9 : ℝ) ^ 3 * Real.log (n : ℝ) ^ 2) *
              ((n : ℝ) /
                (10 * (Q : ℝ) *
                  ((7 / 9 : ℝ) * Real.log (n : ℝ)) ^ 3)) :=
            mul_le_mul_of_nonneg_right herror (by positivity)
          _ = c / 10 * (n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ)) := by
            field_simp [hQpos.ne', hlogN.ne']
      _ ≤ (B : ℝ) - (A : ℝ) := hwidth
  exact ⟨hX₀A, hAB, hwidth, hlogA, hlogB, hBupper, herrorDom⟩

/-- Uniform prime supply for each actual smooth donor, including moving
rational scales all the way up to `floor(n^(2/9))`. -/
theorem exists_eventually_bankOrdinaryPrimeChoices_lower
    {c : ℝ} (hc : 0 < c) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (yNat n : ℚ) →
          ∀ u ∈ bankOrdinarySmoothBulkDonors n Q,
            kappa * secondOrderScale n /
                ((Q : ℝ) * Real.log (n : ℝ)) ≤
              (bankOrdinaryPrimeChoices n
                (upperEndpoint n (upperTailLength c n)) u).card := by
  obtain ⟨C, hC, X₀, hX₀, hshort⟩ :=
    exists_primeInterval_card_lower_from_cumulativePNT
  let kappa : ℝ := c / 40
  refine ⟨kappa, by dsimp only [kappa]; positivity, ?_⟩
  have hgeometry := eventually_bankOrdinary_oneDonor_geometry hc hC X₀
  filter_upwards [hgeometry, eventually_gt_atTop 3] with n hgeom hn
  intro Q hQ hQY u hu
  have hQ0 : 0 ≤ Q := by linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < Q by linarith)
  have huData := (mem_bankOrdinarySmoothBulkDonors hQ0).mp hu
  have hg := hgeom.2.2 Q hQ hQY u huData.1
  let A : ℕ := (2 * n) / u
  let B : ℕ := upperEndpoint n (upperTailLength c n) / u
  change kappa * secondOrderScale n /
      ((Q : ℝ) * Real.log (n : ℝ)) ≤
    (bankPrimeInterval A B).card
  have hprime := hshort A B hg.1 hg.2.1 hg.2.2.2.2.2.2
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogA : 0 < Real.log (A : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 7 / 9) hlogN).trans_le
      hg.2.2.2.1
  have hApos : 0 < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have hlogB : 0 < Real.log (B : ℝ) :=
    hlogA.trans_le (Real.log_le_log hApos
      (by exact_mod_cast hg.2.1))
  calc
    kappa * secondOrderScale n /
        ((Q : ℝ) * Real.log (n : ℝ)) =
      c / 40 * (n : ℝ) /
        ((Q : ℝ) * Real.log (n : ℝ) ^ 2) := by
          dsimp only [kappa, secondOrderScale]
          field_simp
    _ ≤ ((B : ℝ) - (A : ℝ)) /
        (2 * Real.log (B : ℝ)) := by
      have hwidth := hg.2.2.1
      have hlogUpper := hg.2.2.2.2.1
      apply (le_div_iff₀ (mul_pos (by norm_num) hlogB)).2
      calc
        (c / 40 * (n : ℝ) /
            ((Q : ℝ) * Real.log (n : ℝ) ^ 2)) *
              (2 * Real.log (B : ℝ)) ≤
            (c / 40 * (n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ) ^ 2)) *
                (4 * Real.log (n : ℝ)) := by
          have hbase : 0 ≤ c / 40 * (n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ) ^ 2) := by positivity
          apply mul_le_mul_of_nonneg_left _ hbase
          linarith
        _ = c / 10 * (n : ℝ) /
              ((Q : ℝ) * Real.log (n : ℝ)) := by
          field_simp [hQpos.ne', hlogN.ne']; ring
        _ ≤ (B : ℝ) - (A : ℝ) := hwidth
    _ ≤ (bankPrimeInterval A B).card := hprime

/-- Uniform lower bound for the total number of actual ordinary-bank
marker--donor occurrences at every moving large scale. -/
theorem exists_eventually_bankOrdinary_occurrenceTotal_lower
    {c : ℝ} (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (yNat n : ℚ) →
          eta * secondOrderScale n / Real.log (n : ℝ) ≤
            (bankMarkerOccurrenceTotal
              (bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n)) Q) : ℝ) := by
  obtain ⟨delta, hdelta, hdonors⟩ :=
    exists_eventually_bankOrdinarySmoothBulkDonors_lower
  obtain ⟨kappa, hkappa, hprime⟩ :=
    exists_eventually_bankOrdinaryPrimeChoices_lower hc
  let eta : ℝ := delta * kappa
  refine ⟨eta, mul_pos hdelta hkappa, ?_⟩
  have htailSmall : ∀ᶠ n : ℕ in atTop,
      10 * upperTailLength c n ≤ n := by
    have hratio := (upperTailLength_ratio_tendsto_zero hc).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 10))
    filter_upwards [hratio, eventually_gt_atTop 0] with n hn hnpos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hmul : (upperTailLength c n : ℝ) <
        (1 / 10 : ℝ) * (n : ℝ) := (div_lt_iff₀ hnR).mp hn
    have hmulLe : (10 : ℝ) * upperTailLength c n ≤ (n : ℝ) := by
      nlinarith
    exact_mod_cast hmulLe
  filter_upwards [hdonors, hprime, htailSmall,
      eventually_gt_atTop 3, eventually_secondOrderScale_pos] with
      n hdonorN hprimeN htailN hn hscale
  intro Q hQ hQY
  have hQreal : 0 < (Q : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < Q by linarith)
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  let donors := bankOrdinarySmoothBulkDonors n Q
  let M := upperEndpoint n (upperTailLength c n)
  have hM : 10 * M ≤ 21 * n := by
    dsimp only [M, upperEndpoint]
    omega
  have hfinite := sum_bankOrdinaryPrimeChoices_le_occurrenceTotal hQ hM
  have hdonor := hdonorN Q hQ hQY
  have hone : ∀ u ∈ donors,
      kappa * secondOrderScale n /
          ((Q : ℝ) * Real.log (n : ℝ)) ≤
        ((bankOrdinaryPrimeChoices n M u).card : ℝ) := by
    intro u hu
    exact hprimeN Q hQ hQY u hu
  have hsum :
      (donors.card : ℝ) *
          (kappa * secondOrderScale n /
            ((Q : ℝ) * Real.log (n : ℝ))) ≤
        ∑ u ∈ donors, ((bankOrdinaryPrimeChoices n M u).card : ℝ) := by
    calc
      (donors.card : ℝ) *
          (kappa * secondOrderScale n /
            ((Q : ℝ) * Real.log (n : ℝ))) =
        ∑ _u ∈ donors,
          kappa * secondOrderScale n /
            ((Q : ℝ) * Real.log (n : ℝ)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun u hu ↦ hone u hu
  have hsumFinite :
      ∑ u ∈ donors, ((bankOrdinaryPrimeChoices n M u).card : ℝ) ≤
        (bankMarkerOccurrenceTotal
          (bankOrdinaryEligibleRelation n M Q) : ℝ) := by
    exact_mod_cast hfinite
  calc
    eta * secondOrderScale n / Real.log (n : ℝ) =
        (delta * (Q : ℝ)) *
          (kappa * secondOrderScale n /
            ((Q : ℝ) * Real.log (n : ℝ))) := by
      dsimp only [eta]
      field_simp [hQreal.ne', hlogN.ne']
    _ ≤ (donors.card : ℝ) *
          (kappa * secondOrderScale n /
            ((Q : ℝ) * Real.log (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hdonor (by positivity)
    _ ≤ ∑ u ∈ donors,
        ((bankOrdinaryPrimeChoices n M u).card : ℝ) := hsum
    _ ≤ (bankMarkerOccurrenceTotal
        (bankOrdinaryEligibleRelation n M Q) : ℝ) := hsumFinite





/-! ## Marker supply from the exact fiber bound -/



private theorem cast_div_sub_div_le_tail_div_add_one
    {n h P : ℕ} (hP : 0 < P) :
    (((upperEndpoint n h) / P - (2 * n) / P : ℕ) : ℝ) ≤
      (h : ℝ) / (P : ℝ) + 1 := by
  have hAB : (2 * n) / P ≤ upperEndpoint n h / P :=
    Nat.div_le_div_right (two_mul_le_upperEndpoint n h)
  rw [Nat.cast_sub hAB]
  have hupper := cast_natDiv_le_realDiv (upperEndpoint n h) P
  have hlower := realDiv_sub_one_lt_cast_natDiv (2 * n) P hP
  have hupper' : ((upperEndpoint n h / P : ℕ) : ℝ) ≤
      (2 * (n : ℝ)) / (P : ℝ) + (h : ℝ) / (P : ℝ) := by
    calc
      _ ≤ (upperEndpoint n h : ℝ) / (P : ℝ) := hupper
      _ = (2 * (n : ℝ)) / (P : ℝ) + (h : ℝ) / (P : ℝ) := by
        rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hlower' : (2 * (n : ℝ)) / (P : ℝ) - 1 <
      (((2 * n) / P : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlower
  calc
    ((upperEndpoint n h / P : ℕ) : ℝ) - (((2 * n) / P : ℕ) : ℝ) ≤
        ((2 * (n : ℝ)) / (P : ℝ) + (h : ℝ) / (P : ℝ)) -
          ((2 * (n : ℝ)) / (P : ℝ) - 1) :=
      sub_le_sub hupper' hlower'.le
    _ = (h : ℝ) / (P : ℝ) + 1 := by ring

private theorem eventually_bankOrdinary_multiplicity_le_cap
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
      20 < Q → Q ≤ (yNat n : ℚ) →
        0 < bankOrdinaryMultiplicityCap c n Q ∧
        ∀ P ∈ bankEligibleMarkers
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n)) Q),
          bankDonorMultiplicity
              (bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n)) Q) P ≤
            bankOrdinaryMultiplicityCap c n Q := by
  have htailUpper : ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) / secondOrderScale n ≤ 2 * c :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_le_nhds (by linarith : c < 2 * c))
  filter_upwards [htailUpper, eventually_secondOrderScale_pos,
      eventually_gt_atTop 3] with n htail hscale hn
  intro Q hQ _hQY
  have hQposRat : (0 : ℚ) < Q := by linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQposRat
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hcapPos : 0 < bankOrdinaryMultiplicityCap c n Q := by
    have hone : (1 : ℝ) ≤
        2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2 := by
      have : 0 < 2 * c * (Q : ℝ) / Real.log (n : ℝ) := by positivity
      linarith
    have hceil : (1 : ℝ) ≤
        (⌈2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2⌉₊ : ℝ) :=
      hone.trans (Nat.le_ceil _)
    exact_mod_cast hceil
  refine ⟨hcapPos, ?_⟩
  intro P hPmarker
  rcases Finset.mem_image.mp hPmarker with ⟨⟨P', u⟩, hpair, hfirst⟩
  dsimp only [Prod.fst] at hfirst
  subst P'
  have hpData := mem_bankOrdinaryEligibleRelation.mp hpair
  have hPpos : 0 < P := hpData.2.1.pos
  have hmarker := hpData.2.2.2.1
  have hfiber := bankOrdinary_donorMultiplicity_le_div_sub_div
    (n := n) (M := upperEndpoint n (upperTailLength c n))
    (Q := Q) hPpos
  have hfiberCast :
      (bankDonorMultiplicity
        (bankOrdinaryEligibleRelation n
          (upperEndpoint n (upperTailLength c n)) Q) P : ℝ) ≤
        (upperTailLength c n : ℝ) / (P : ℝ) + 1 := by
    have hfiberR :
        (bankDonorMultiplicity
          (bankOrdinaryEligibleRelation n
            (upperEndpoint n (upperTailLength c n)) Q) P : ℝ) ≤
          (((upperEndpoint n (upperTailLength c n)) / P -
            (2 * n) / P : ℕ) : ℝ) := by
      exact_mod_cast hfiber
    exact hfiberR.trans (cast_div_sub_div_le_tail_div_add_one hPpos)
  have htailCast : (upperTailLength c n : ℝ) ≤
      2 * c * secondOrderScale n :=
    (div_le_iff₀ hscale).mp htail
  have hmarkerQ :
      4 * (n : ℝ) < 3 * (Q : ℝ) * (P : ℝ) := by
    exact_mod_cast hmarker.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hPcast : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hratio :
      (upperTailLength c n : ℝ) / (P : ℝ) ≤
        3 * c / 2 * (Q : ℝ) / Real.log (n : ℝ) := by
    rw [secondOrderScale] at htailCast
    apply (div_le_iff₀ hPcast).2
    calc
      (upperTailLength c n : ℝ) ≤
          2 * c * ((n : ℝ) / Real.log (n : ℝ)) := htailCast
      _ ≤ (3 * c / 2 * (Q : ℝ) / Real.log (n : ℝ)) * (P : ℝ) := by
        field_simp [hlogN.ne']
        nlinarith [hmarkerQ]
  have htoCeil :
      (bankDonorMultiplicity
        (bankOrdinaryEligibleRelation n
          (upperEndpoint n (upperTailLength c n)) Q) P : ℝ) ≤
        (bankOrdinaryMultiplicityCap c n Q : ℝ) := by
    calc
      _ ≤ (upperTailLength c n : ℝ) / (P : ℝ) + 1 := hfiberCast
      _ ≤ 2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2 := by
        have hnonneg : 0 ≤ c * (Q : ℝ) / Real.log (n : ℝ) := by positivity
        have hratio' : (upperTailLength c n : ℝ) / (P : ℝ) ≤
            (3 / 2 : ℝ) * (c * (Q : ℝ) / Real.log (n : ℝ)) := by
          calc
            _ ≤ 3 * c / 2 * (Q : ℝ) / Real.log (n : ℝ) := hratio
            _ = (3 / 2 : ℝ) *
                (c * (Q : ℝ) / Real.log (n : ℝ)) := by ring
        calc
          (upperTailLength c n : ℝ) / (P : ℝ) + 1 ≤
              (3 / 2 : ℝ) *
                (c * (Q : ℝ) / Real.log (n : ℝ)) + 1 :=
            by simpa only [add_comm] using add_le_add_right hratio' 1
          _ ≤ 2 * (c * (Q : ℝ) / Real.log (n : ℝ)) + 2 := by
            nlinarith
          _ = 2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2 := by ring
      _ ≤ (bankOrdinaryMultiplicityCap c n Q : ℝ) := by
        exact Nat.le_ceil _
  exact_mod_cast htoCeil



/-- The paper's marker-signature lower bound
`K_Q ≫_c (n/log n)/max(Q,log n)`, uniformly for fixed or moving
`20 < Q ≤ n^(2/9)`. -/
theorem exists_eventually_bankOrdinary_markerCount_lower
    {c : ℝ} (hc : 0 < c) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (yNat n : ℚ) →
          rho * secondOrderScale n /
              max (Q : ℝ) (Real.log (n : ℝ)) ≤
            (bankEligibleMarkerCount
              (bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n)) Q) : ℝ) := by
  obtain ⟨eta, heta, hoccurrence⟩ :=
    exists_eventually_bankOrdinary_occurrenceTotal_lower hc
  let D : ℝ := 4 * c + 6
  have hD : 0 < D := by dsimp only [D]; positivity
  let rho : ℝ := eta / D
  refine ⟨rho, div_pos heta hD, ?_⟩
  have hmultiplicity := eventually_bankOrdinary_multiplicity_le_cap hc
  filter_upwards [hoccurrence, hmultiplicity,
      eventually_gt_atTop 3] with n hocc hmult hn
  intro Q hQ hQY
  let eligible := bankOrdinaryEligibleRelation n
    (upperEndpoint n (upperTailLength c n)) Q
  let m := bankOrdinaryMultiplicityCap c n Q
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (show (0 : ℚ) < Q by linarith)
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hmaxPos : 0 < max (Q : ℝ) (Real.log (n : ℝ)) :=
    lt_of_lt_of_le hQpos (le_max_left _ _)
  have hmData := hmult Q hQ hQY
  have hfinite := bankMarkerOccurrenceTotal_le_mul_markerCount
    eligible m hmData.2
  have hmUpper : (m : ℝ) ≤
      D * max (Q : ℝ) (Real.log (n : ℝ)) /
        Real.log (n : ℝ) := by
    have hceil : (m : ℝ) <
        2 * c * (Q : ℝ) / Real.log (n : ℝ) + 3 := by
      dsimp only [m, bankOrdinaryMultiplicityCap]
      convert
        (Nat.ceil_lt_add_one
          (by positivity : (0 : ℝ) ≤
            2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2)) using 1
      ring
    have hqMax : (Q : ℝ) ≤
        max (Q : ℝ) (Real.log (n : ℝ)) := le_max_left _ _
    have hlogMax : Real.log (n : ℝ) ≤
        max (Q : ℝ) (Real.log (n : ℝ)) := le_max_right _ _
    dsimp only [D]
    apply hceil.le.trans
    apply (le_div_iff₀ hlogN).2
    calc
      (2 * c * (Q : ℝ) / Real.log (n : ℝ) + 3) *
          Real.log (n : ℝ) =
        2 * c * (Q : ℝ) + 3 * Real.log (n : ℝ) := by
          field_simp [hlogN.ne']
      _ ≤ 2 * c * max (Q : ℝ) (Real.log (n : ℝ)) +
          3 * max (Q : ℝ) (Real.log (n : ℝ)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hqMax (by positivity))
          (mul_le_mul_of_nonneg_left hlogMax (by norm_num))
      _ ≤ (4 * c + 6) * max (Q : ℝ) (Real.log (n : ℝ)) := by
        have hmaxNonneg : 0 ≤ max (Q : ℝ) (Real.log (n : ℝ)) := hmaxPos.le
        have hc2 : 2 * c ≤ 4 * c := by linarith
        have hthree : (3 : ℝ) ≤ 6 := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hc2 hmaxNonneg,
          mul_le_mul_of_nonneg_right hthree hmaxNonneg]
  have hoccLower := hocc Q hQ hQY
  have hfiniteR :
      (bankMarkerOccurrenceTotal eligible : ℝ) ≤
        (m : ℝ) * (bankEligibleMarkerCount eligible : ℝ) := by
    exact_mod_cast hfinite
  have hupper :
      (bankMarkerOccurrenceTotal eligible : ℝ) ≤
        (D * max (Q : ℝ) (Real.log (n : ℝ)) /
          Real.log (n : ℝ)) *
            (bankEligibleMarkerCount eligible : ℝ) := by
    exact hfiniteR.trans (mul_le_mul_of_nonneg_right hmUpper (by positivity))
  change rho * secondOrderScale n /
      max (Q : ℝ) (Real.log (n : ℝ)) ≤
    (bankEligibleMarkerCount eligible : ℝ)
  dsimp only [rho]
  have hcombined :
      eta * secondOrderScale n / Real.log (n : ℝ) ≤
        (D * max (Q : ℝ) (Real.log (n : ℝ)) /
          Real.log (n : ℝ)) *
            (bankEligibleMarkerCount eligible : ℝ) :=
    hoccLower.trans hupper
  have hcancel := mul_le_mul_of_nonneg_right hcombined hlogN.le
  field_simp [hlogN.ne'] at hcancel
  calc
    eta / D * secondOrderScale n /
        max (Q : ℝ) (Real.log (n : ℝ)) =
      (eta * secondOrderScale n) /
        (D * max (Q : ℝ) (Real.log (n : ℝ))) := by
          field_simp [hD.ne', hmaxPos.ne']
    _ ≤ (bankEligibleMarkerCount eligible : ℝ) := by
      apply (div_le_iff₀ (mul_pos hD hmaxPos)).2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hcancel

/-! ## The five fixed nonbottom scales -/

















end

end Erdos390.WholePaper

end

theorem solution :
∀ {c : Real},
  LT.lt.{0} (0 : Real) c →
    ∃ rho,
      And (LT.lt.{0} (0 : Real) rho)
        (∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∀ (Q : Rat),
            LT.lt.{0} (20 : Rat) Q →
              LE.le.{0} Q ↑(Erdos390.Full.ArithmeticModel.yNat n) →
                LE.le.{0}
                  (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} rho (Erdos390.WholePaper.secondOrderScale n))
                    (Max.max.{0} (↑Q) (Real.log ↑n)))
                  ↑(Erdos390.WholePaper.bankEligibleMarkerCount.{0, 0}
                      (Erdos390.WholePaper.bankOrdinaryEligibleRelation n
                        (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) Q))) := by
  exact @Erdos390.WholePaper.exists_eventually_bankOrdinary_markerCount_lower
