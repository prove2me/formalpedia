-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalActualSelectorMassEstimate_of_topFrozenBalancedInitial_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.421004+00:00
-- url     : https://prove2.me/submissions/6b9622e5-bf4e-4ead-a338-9941ea8b198b

import Definitions.Def_erdos390_remaining_analytic_propositions_004
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalBalancedRawSmoothRowDiscrepancy_isBigO_compact
import Theorems.Thm_Erdos390_WholePaper_bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
import Theorems.Thm_Erdos390_WholePaper_eventually_roughCanonicalActiveIntrinsicRawBroadSurplus_compact
import Theorems.Thm_Erdos390_WholePaper_fullCentralAnchors_completeRoughLabel_injective_of_ne_one



section
theorem Erdos390.WholePaper.eventually_roughCanonicalActiveIntrinsicRawBroadSurplus : Erdos390.RemainingAnalyticGoal008_006 := @Erdos390.WholePaper.eventually_roughCanonicalActiveIntrinsicRawBroadSurplus_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalBalancedRawSmoothRowDiscrepancy_isBigO : Erdos390.RemainingAnalyticGoal004_010 := @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalBalancedRawSmoothRowDiscrepancy_isBigO_compact
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











theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.Scale -/
section


/-!
# Exact scale identities

This file records the elementary identities behind the fixed choice
`y = n^(2/9)` used throughout the marked and smooth bridge.  Keeping them as
equalities avoids repeatedly treating `U = 9/2` and the four-mark cofactor
margin as informal arithmetic simplifications.
-/

open Filter Topology

namespace Erdos390.Full.Scale

open ArithmeticModel

























theorem endpointRatio_eq {n : ℕ} (hn : 0 < n) :
    endpointRatio n = L n ^ 2 / (n : ℝ) ^ (5 / 9 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      (n : ℝ) ^ (4 / 9 : ℝ) * (n : ℝ) ^ (5 / 9 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  rw [endpointRatio, y_pow_two]
  field_simp [(Real.rpow_pos_of_pos hnR (5 / 9 : ℝ)).ne', hnR.ne']
  nlinarith

/-- In particular, all `y^2 L^2 / n` endpoint errors vanish. -/
theorem tendsto_endpointRatio_zero :
    Tendsto endpointRatio atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (5 / 9 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 5 / 9)).tendsto_div_nhds_zero
  have hnat : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (5 / 9 : ℝ))
      atTop (𝓝 0) := by
    simpa [Real.rpow_natCast] using hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa [L] using (endpointRatio_eq hn).symm

end Erdos390.Full.Scale

end

/- Source module: Erdos390.WholePaper.StationaryLayers -/
section


/-!
# Stationary prime layers

For a fixed row `r`, Section 3 uses the prime interval
`n / (r + 1) < p ≤ 2n / (2r + 1)`.  The definition below records the
endpoints by cross-multiplied natural-number inequalities, so there is no
rounding ambiguity.  Its cardinality is then identified with the exact
prime-counting difference to which the fixed-interval PNT applies.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section



@[simp]
theorem mem_stationaryPrimeLayer {n r p : ℕ} :
    p ∈ stationaryPrimeLayer n r ↔
      p.Prime ∧ n < p * (r + 1) ∧ p * (2 * r + 1) ≤ 2 * n := by
  simp only [stationaryPrimeLayer, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun hp ↦ hp.2
  · intro hp
    have hpLe : p ≤ 2 * n :=
      (Nat.le_mul_of_pos_right p (by omega : 0 < 2 * r + 1)).trans hp.2.2
    exact ⟨by omega, hp⟩

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPromotion -/
section


/-! # Promotion of residual central prime powers

This file formalizes the elementary promotion step from Section 10 of the
paper.  A positive block `B ≤ 2n` is multiplied by the least power of two
which puts it above `n`; the resulting block still lies at most `2n`.
-/

namespace Erdos390.WholePaper

noncomputable section





theorem promotionExponent_spec {n B : ℕ} (hB : 0 < B) :
    n < 2 ^ promotionExponent n B * B := by
  have htarget : n / B + 1 ≤ 2 ^ promotionExponent n B := by
    simpa only [promotionExponent] using
      Nat.le_pow_clog Nat.one_lt_two (n / B + 1)
  apply (Nat.div_lt_iff_lt_mul hB).mp
  omega

theorem promotionExponent_minimal {n B k : ℕ}
    (hk : k < promotionExponent n B) :
    2 ^ k * B ≤ n := by
  have hpow : 2 ^ k < n / B + 1 := by
    exact (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp hk
  have hpow' : 2 ^ k ≤ n / B := by omega
  exact (Nat.mul_le_mul_right B hpow').trans (Nat.div_mul_le_self n B)

theorem promotedBlock_gt {n B : ℕ} (hB : 0 < B) :
    n < promotedBlock n B := by
  exact promotionExponent_spec hB

theorem promotedBlock_le_two_mul {n B : ℕ}
    (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    promotedBlock n B ≤ 2 * n := by
  by_cases hBn : B ≤ n
  · have hdivPos : 0 < n / B := Nat.div_pos hBn hB
    have htarget : 1 < n / B + 1 := by omega
    have hkPos : 0 < promotionExponent n B := by
      simpa only [promotionExponent] using
        Nat.clog_pos Nat.one_lt_two htarget
    have hkPred : promotionExponent n B - 1 < promotionExponent n B := by
      omega
    have hprevious : 2 ^ (promotionExponent n B - 1) * B ≤ n :=
      promotionExponent_minimal hkPred
    have hkSplit : promotionExponent n B - 1 + 1 = promotionExponent n B := by
      omega
    rw [promotedBlock, ← hkSplit, pow_succ]
    calc
      (2 ^ (promotionExponent n B - 1) * 2) * B =
          2 * (2 ^ (promotionExponent n B - 1) * B) := by ac_rfl
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hprevious
  · have hnB : n < B := Nat.lt_of_not_ge hBn
    have hdiv : n / B = 0 := Nat.div_eq_of_lt hnB
    simp [promotedBlock, promotionExponent, hdiv, hBupper]

theorem promotedBlock_mem_centralInterval {n B : ℕ}
    (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    promotedBlock n B ∈ Finset.Ioc n (2 * n) := by
  exact Finset.mem_Ioc.mpr
    ⟨promotedBlock_gt hB, promotedBlock_le_two_mul hB hBupper⟩





theorem centralPrimeBlock_pos (n p : ℕ) : 0 < centralPrimeBlock n p := by
  cases p with
  | zero => simp [centralPrimeBlock]
  | succ p =>
      simpa only [centralPrimeBlock] using
        (pow_pos (Nat.succ_pos p)
          ((Nat.choose (2 * n) n).factorization (p + 1)))

theorem centralPrimeBlock_le_two_mul {n p : ℕ} (hn : 0 < n) :
    centralPrimeBlock n p ≤ 2 * n := by
  simpa only [centralPrimeBlock] using
    (Nat.pow_factorization_choose_le
      (p := p) (n := 2 * n) (k := n) (by omega))







theorem promotedCentralFactor_mem_centralInterval {n p : ℕ} (hn : 0 < n) :
    promotedCentralFactor n p ∈ Finset.Ioc n (2 * n) := by
  exact promotedBlock_mem_centralInterval
    (centralPrimeBlock_pos n p) (centralPrimeBlock_le_two_mul hn)

theorem promotedCentralFactor_gt {n p : ℕ} (hn : 0 < n) :
    n < promotedCentralFactor n p :=
  (Finset.mem_Ioc.mp (promotedCentralFactor_mem_centralInterval hn)).1











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ResidualCentralFactors -/
section


/-! # The finite family of promoted residual central factors -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section











theorem residualCentralPrimes_exponent_pos {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) :
    0 < (Nat.choose (2 * n) n).factorization p := by
  have hpMem : p ∈ (Nat.choose (2 * n) n).primeFactors :=
    (Finset.mem_filter.mp hp).1
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  exact (Nat.prime_of_mem_primeFactors hpMem).factorization_pos_of_dvd
    hchoosePos.ne' (Nat.dvd_of_mem_primeFactors hpMem)









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPrimeBlockDecomposition -/
section


/-!
# Exact low/high decomposition of the central binomial coefficient

The central binomial coefficient is the product of its complete prime-power
blocks.  Splitting those blocks at the anchor cutoff and promoting every low
block therefore introduces exactly one aggregate power of two and no other
valuation error.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem largeCentralPrimes_prime {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : p.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem largeCentralPrimes_gt {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : X < p :=
  (Finset.mem_filter.mp hp).2











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralCarryAnchors -/
section


/-! # Exact arithmetic of the fixed-prefix central carry anchors -/

namespace Erdos390.WholePaper

noncomputable section





/-- Every allowed allocation cofactor places its carry prime anchor in the
central interval. -/
theorem stationaryPrimeLayer_mul_cofactor_mem_centralInterval
    {n r p q : ℕ} (hp : p ∈ stationaryPrimeLayer n r)
    (hqLower : r + 1 ≤ q) (hqUpper : q ≤ 2 * r + 1) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  have hmem := mem_stationaryPrimeLayer.mp hp
  apply Finset.mem_Ioc.mpr
  constructor
  · exact hmem.2.1.trans_le (Nat.mul_le_mul_left p hqLower)
  · exact (Nat.mul_le_mul_left p hqUpper).trans hmem.2.2



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorProduct -/
section


/-!
# Exact product of all three central-anchor families

This file isolates the finite algebra behind the full central-anchor lemma.
For every large central prime, a cofactor choice is required to follow either
its row-zero route or its stationary carry row.  The resulting marker factors
are combined with every promoted low prime-power block.  Their product is
proved to be the central binomial coefficient times the literal cofactor and
promotion divisor.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem routedCentralCofactor_mem_centralInterval
    {n p q : ℕ} (hq : IsRoutedCentralCofactor n p q) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  rcases hq with hzero | ⟨r, _hrPos, _hr, hpRow, hqLower, hqUpper⟩
  · simpa only [hzero.2.2, mul_one] using
      (show p ∈ Finset.Ioc n (2 * n) from
        Finset.mem_Ioc.mpr ⟨hzero.1, hzero.2.1⟩)
  · exact stationaryPrimeLayer_mul_cofactor_mem_centralInterval
      hpRow hqLower hqUpper









theorem largeCentralAnchor_mem_centralInterval
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n X) :
    largeCentralAnchor q p ∈ Finset.Ioc n (2 * n) := by
  exact routedCentralCofactor_mem_centralInterval (hq p hp)























end

end Erdos390.WholePaper

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













/-- The upper tail is disjoint from every raw lower candidate. -/
theorem roughUpperBlock_disjoint_rawCandidateSet
    (n h K : ℕ) :
    Disjoint (roughUpperBlock n h) (roughRawCandidateSet n h K) := by
  rw [Finset.disjoint_left]
  intro a haUpper haLower
  simp only [roughUpperBlock, roughRawCandidateSet,
    roughHighLowerBlock, roughBroadLowerBlock, Finset.mem_Ioc,
    Finset.mem_union] at haUpper haLower
  rcases haLower with haHigh | haBroad <;> omega







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





/-! ## The complementary low-prime factorization -/















/-! ## Uniqueness and the smooth-label criterion -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomMarkerPools -/
section


/-!
# Literal marker pools for the four bottom bank moves

The four rows below are the natural-number half-open intervals appearing in
the paper.  Each is split at its integer midpoint into two fixed one-half
orientation subintervals.  This file proves only exact finite interval and
factor arithmetic; prime supply is deliberately kept separate.
-/

namespace Erdos390.WholePaper

noncomputable section











































/-- A marker in its row makes both endpoint states and the donor lie in
the factor interval `(n,M]`. -/
theorem bankBottom_states_donor_mem_factorInterval
    {n M marker : ℕ} {move : BankBottomMove}
    (hmarker : marker ∈ bankBottomMarkerInterval n M move) :
    bankBottomLowerState move marker ∈ factorInterval n M ∧
      bankBottomUpperState move marker ∈ factorInterval n M ∧
      bankBottomDonor move marker ∈ factorInterval n M := by
  cases move <;>
    simp only [bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, bankBottomLowerState,
      bankBottomUpperState, bankBottomDonor,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier, factorInterval] at hmarker ⊢ <;>
    omega



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomPaperComponents -/
section


/-!
# Actual bottom-bank components from the concrete marker matching

The capacity argument deliberately matches the rectangular upper-bound family
consisting of every signed slot and all four bottom rows.  The path belonging
to a small source prime does not use every one of those rows: source `3` uses
only `3→2→1`, and source `2` uses only `2→1`.  This file therefore separates
the full matched family from the literal relevant subfamily before forming any
set of used occurrences.

For every matched request we retain its actual prime marker, the two state
factors in the corresponding row, and its donor occurrence.  A finite set of
occurrence values is used, so in the last two rows the donor and the upper
state are literally one occurrence, rather than two tagged copies.  The only
global input is the already constructed injective marker matching.  All other
claims below are explicit interval, factorization, and large-prime arithmetic.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal relevant subfamily -/





















































/-! ## The deterministic truncated bottom path -/

























/-! ## A realization obtained from the actual matching -/





namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)





















/-- Both row endpoints and the donor are actual factors in `(n,M]`. -/
theorem states_donor_mem_factorInterval (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.lowerStateFactor request ∈ factorInterval n M ∧
      realization.upperStateFactor request ∈ factorInterval n M ∧
      realization.donorFactor request ∈ factorInterval n M := by
  simpa only [lowerStateFactor, upperStateFactor, donorFactor] using
    bankBottom_states_donor_mem_factorInterval
      (realization.marker_mem_row hTwoN request)







/-! The four paper rows, with the marker made explicit. -/













/-! ## Orientation-aware realized row and slot changes -/























end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/









namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)























































end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/



namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)









/-! ## Relevant markers and marker-to-component uniqueness -/



























end BankBottomPaperRealization

/-! ## Cardinality bound for the actual relevant marker set -/







/-! ## Eventual local geometry and the terminal realized family -/

private theorem bankBottom_yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

theorem eventually_bankBottom_six_le_yNat :
    ∀ᶠ n : ℕ in atTop, 6 ≤ yNat n :=
  bankBottom_yNat_tendsto_atTop.eventually (eventually_ge_atTop 6)





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryPaperComponents -/
section


/-!
# Realized ordinary bank components

An ordinary matching supplies an actual pair `(P,u)` to every concrete path
request `q→b`.  This file materializes the three factor occurrences

* source state `P*q`,
* target state `P*b`, and
* backing donor `P*u`.

All three lie in `(n,M]` and have the same complete rough signature.  The
large prime marker is recovered uniquely from any realized occurrence, which
gives marker injectivity, donor-product injectivity, and collision-freedom
across requests, scales, and orientations.  Finally, cancellation of the
common marker turns the realized component changes back into the actual
finite path telescope.

The public names intentionally mirror `BankBottomPaperComponents`: a
realization object, factor-valued methods, an occurrence-kind enumeration,
and `occurrenceValue`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Coarse global size bounds -/













/-! ## Arithmetic helpers for rough signatures -/









/-! ## Marker injectivity inherited from the orientation pools -/









/-! ## The public realization object and its actual factors -/



namespace BankOrdinaryPaperRealization





































theorem donorValue_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.donorValue request ∈ factorInterval n M := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  simp only [donorValue, factorInterval, Finset.mem_Ioc]
  have hlower := heligible.2.2.2.2.2.2.1
  change 2 * n < R.marker request * R.donorCore request at hlower
  exact ⟨by omega, heligible.2.2.2.2.2.2.2⟩





































/-! ## The three actual occurrences and global collision-freedom -/





theorem two_mul_n_lt_donorValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    2 * n < R.donorValue request :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.2.2.2.2.2.1

































/-! ## Realized component and signed-slot changes -/























end BankOrdinaryPaperRealization

/-! ## Eventual realized allocation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperComponents -/
section


/-!
# Combined bottom and ordinary bank realization

This file is only the composition layer.  The two allocation mechanisms stay
independent, but their marker ranges are strictly separated:

`3 * ordinaryMarker < n < 3 * bottomMarker`.

Consequently the marker maps remain injective after the two request families
are joined.  Prime-marker recovery also turns this strict separation into
cross-family disjointness of the actual state/donor occurrence sets.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section





namespace BankPaperRealization





/-- Marker assignment is globally injective after adjoining the relevant
bottom requests and all ordinary requests. -/
theorem marker_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.marker := by
  intro request request' hmarker
  cases request with
  | inl bottomRequest =>
      cases request' with
      | inl bottomRequest' =>
          have hrequest : bottomRequest = bottomRequest' :=
            R.bottom.relevantMarkerMap_injective
              (by simpa only [marker] using hmarker)
          exact congrArg Sum.inl hrequest
      | inr ordinaryRequest =>
          exfalso
          have hlt := R.ordinaryMarker_lt_bottomMarker ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)
          simp only [marker] at hmarker
          omega
  | inr ordinaryRequest =>
      cases request' with
      | inl bottomRequest =>
          exfalso
          have hlt := R.ordinaryMarker_lt_bottomMarker ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)
          simp only [marker] at hmarker
          omega
      | inr ordinaryRequest' =>
          have hrequest : ordinaryRequest = ordinaryRequest' :=
            R.ordinary.marker_injective
              (by simpa only [marker] using hmarker)
          exact congrArg Sum.inr hrequest











/-! ## Cross-family actual occurrence disjointness -/

















end BankPaperRealization

/-! ## Terminal combined realization -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorCutoff -/
section


/-!
# The fixed-prefix central-anchor cutoff

For a fixed prefix depth `R`, the paper splits the central prime blocks at
`n / (R + 1)`.  This file gives an explicit sufficient threshold for all
scale separations and then connects that literal cutoff directly to the
large-prime routing and central-anchor product APIs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section





theorem centralAnchorCutoffThreshold_pos (R : ℕ) :
    0 < centralAnchorCutoffThreshold R := by
  simp [centralAnchorCutoffThreshold]

/-- At the explicit threshold, the cutoff is at least `4(R+1)`. -/
theorem four_mul_succ_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    4 * (R + 1) ≤ centralAnchorCutoff R n := by
  rw [centralAnchorCutoff, Nat.le_div_iff_mul_le (by omega)]
  simpa only [centralAnchorCutoffThreshold, pow_two, mul_assoc] using hn



/-- The explicit threshold also puts `2n` strictly below the cutoff square. -/
theorem two_mul_lt_centralAnchorCutoff_sq
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * n < (centralAnchorCutoff R n) ^ 2 := by
  let X := centralAnchorCutoff R n
  have hX : 4 * (R + 1) ≤ X := by
    simpa only [X] using four_mul_succ_le_centralAnchorCutoff hn
  have hXPos : 0 < X := by omega
  have hnUpper : n < (R + 1) * (X + 1) := by
    simpa only [X, centralAnchorCutoff] using
      Nat.lt_mul_div_succ n (by omega : 0 < R + 1)
  have hlinear : 2 * (R + 1) * (X + 1) ≤ X ^ 2 := by
    calc
      2 * (R + 1) * (X + 1) ≤ 2 * (R + 1) * (2 * X) := by
        exact Nat.mul_le_mul_left (2 * (R + 1)) (by omega)
      _ = (4 * (R + 1)) * X := by ring
      _ ≤ X * X := Nat.mul_le_mul_right X hX
      _ = X ^ 2 := by ring
  calc
    2 * n < 2 * ((R + 1) * (X + 1)) :=
      (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
    _ = 2 * (R + 1) * (X + 1) := by ring
    _ ≤ X ^ 2 := hlinear







































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrecharge -/
section


/-!
# The actual precharged bank state

This module is independent of the eventual path selector.  Its component
index is the already realized global request type: every relevant bottom row
and every ordinary row occurs exactly once.  For each component we expose its
orientation-aware base and alternate states and its actual donor occurrence.

The proofs below use only the explicit component geometry.  In particular,
there is no abstract capacity or compatibility hypothesis: global
injectivity follows from the realized occurrence-set disjointness, and the
donor tail is the literal interval `(2n,M]`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section



namespace BankBottomPaperRealization

/-- Every actual bottom donor is in the strict tail above `2n`. -/
theorem two_mul_n_lt_donorFactor
    {n M : ℕ} (R : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    2 * n < R.donorFactor request := by
  have hrow := R.marker_mem_row hTwoN request
  cases hmove : R.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, donorFactor,
      bankBottomDonor, bankBottomDonorMultiplier] at hrow ⊢ <;> omega

end BankBottomPaperRealization

namespace BankPaperRealization

attribute [local instance] Erdos390.WholePaper.BankPaperRealization.bankPaperMarkerRequestDecidableEq

/-! ## Global component data -/

























/-! ## Complete rough signatures -/







/-! ## Endpoint and donor injectivity -/





















/-! ## Literal finite states, donor tail, and replacement map -/

























/-- Every donor, ordinary or bottom, is an actual factor in `(2n,M]`. -/
theorem prechargeDonorValue_mem_tail
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ Finset.Ioc (2 * n) M := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      have hlower := R.bottom.two_mul_n_lt_donorFactor
        R.ordinary.two_mul_n_le_M fullRequest
      have hupper : R.bottom.donorFactor fullRequest ≤ M := by
        have hdata : n < R.bottom.donorFactor fullRequest ∧
            R.bottom.donorFactor fullRequest ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.bottom.states_donor_mem_factorInterval
              R.ordinary.two_mul_n_le_M fullRequest).2.2
        exact hdata.2
      simpa only [prechargeDonorValue, fullRequest,
        Finset.mem_Ioc] using And.intro hlower hupper
  | inr request =>
      have hlower := R.ordinary.two_mul_n_lt_donorValue request
      have hupper : R.ordinary.donorValue request ≤ M := by
        have hdata : n < R.ordinary.donorValue request ∧
            R.ordinary.donorValue request ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.ordinary.donorValue_mem_factorInterval request)
        exact hdata.2
      simpa only [prechargeDonorValue, Finset.mem_Ioc] using
        And.intro hlower hupper

theorem prechargeDonorSet_subset_tail
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet ⊆ Finset.Ioc (2 * n) M := by
  intro donor hdonor
  rw [prechargeDonorSet, indexedPathState, Finset.mem_image] at hdonor
  obtain ⟨request, _hrequest, rfl⟩ := hdonor
  exact R.prechargeDonorValue_mem_tail request





















/-! ## Component counts and the base product -/























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalBacking -/
section


/-!
# The literal fixed exceptional factors and their high-prime backing

The paper fixes every upper-tail factor whose complete rough row has real
scale `2n / R_y(a) < n ^ deltaStar`, except for the actual donor occurrences
already withheld for the precharged bank.  This file makes that set literal.

The definition deliberately uses the displayed real quotient and real power.
It is not the larger integral test obtained by flooring the rough scale and
ceiling the exceptional cutoff.

At every prime above the rough cutoff, replacing the donor set by the bank's
base state preserves factorization coordinatewise.  The fixed exceptional
factors and donors are disjoint subsets of the literal tail, so their union
is an unconditional backing product for the complete selector charge in
all such coordinates.  No small-prime charge estimate is asserted here.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section







namespace BankPaperRealization





theorem paperFixedExceptionalFactors_subset_upperBlock
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆ roughUpperBlock n h := by
  intro a ha
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at ha
  exact (mem_paperExceptionalUpperFactors.mp ha.1).1





















end BankPaperRealization

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



















/-- Filtering after deleting the guards is the same as deleting the guards
inside each raw complete rough row. -/
theorem roughCanonicalGuardedRow_eq_rawRow_sdiff_guardSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardedRow certificate deltaStar K label =
      completeRoughRowFiber (yNat n)
          (roughRawCandidateSet n h K) label \
        R.roughCanonicalGuardSet certificate deltaStar := by
  ext a
  simp only [roughCanonicalGuardedRow,
    roughCanonicalGuardedCandidateSet, mem_completeRoughRowFiber,
    Finset.mem_sdiff]
  tauto

/-- The surviving and deleted parts are disjoint. -/
theorem roughCanonicalGuardedRow_disjoint_guardDeletedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    Disjoint
      (R.roughCanonicalGuardedRow certificate deltaStar K label)
      (R.roughCanonicalGuardDeletedRow certificate deltaStar K label) := by
  rw [Finset.disjoint_left]
  intro a haGuarded haDeleted
  rw [R.roughCanonicalGuardedRow_eq_rawRow_sdiff_guardSet
    certificate deltaStar K label, Finset.mem_sdiff] at haGuarded
  rw [roughCanonicalGuardDeletedRow, Finset.mem_inter] at haDeleted
  exact haGuarded.2 haDeleted.2

/-- The two row pieces exhaust the original raw row. -/
theorem roughCanonicalGuardedRow_union_guardDeletedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardedRow certificate deltaStar K label ∪
        R.roughCanonicalGuardDeletedRow certificate deltaStar K label =
      completeRoughRowFiber (yNat n)
        (roughRawCandidateSet n h K) label := by
  rw [R.roughCanonicalGuardedRow_eq_rawRow_sdiff_guardSet
    certificate deltaStar K label]
  ext a
  simp only [roughCanonicalGuardDeletedRow, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- Exact additive decomposition of any real row mass into its surviving
and guard-deleted parts. -/
theorem sum_roughCanonicalGuardedRow_add_sum_guardDeletedRow
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) (x : ℕ → ℝ) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        x a) +
      ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
        K label, x a =
      ∑ a ∈ completeRoughRowFiber (yNat n)
        (roughRawCandidateSet n h K) label, x a := by
  rw [← Finset.sum_union
      (R.roughCanonicalGuardedRow_disjoint_guardDeletedRow
        certificate deltaStar K label),
    R.roughCanonicalGuardedRow_union_guardDeletedRow
      certificate deltaStar K label]

/-! ## The donor/base row-preserving bijection -/









/-! ## Upper-tail ownership and the postcharge target -/





























/-! ## Exact local discrepancy ledger -/





/-- Exact guard-local ledger.  It is purely the identity
`raw row = surviving row ⊔ deleted row` together with the definition of
the postcharge quota. -/
theorem roughCanonicalGuardLocalDiscrepancyLedger
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) (x : ℕ → ℝ) :
    R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
        K label x -
      roughCanonicalRawRowDiscrepancy n h K label x =
      -(completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label : ℝ) -
        (completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : ℝ) +
        ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
          K label, x a := by
  rw [roughCanonicalPostchargeRowDiscrepancy,
    roughCanonicalRawRowDiscrepancy,
    roughCanonicalPostchargeRowTarget,
    ← R.sum_roughCanonicalGuardedRow_add_sum_guardDeletedRow
      certificate deltaStar K label x]
  ring

/-! ## Exact support reduction for the local deletion set -/

/-- Fixed exceptional factors cannot themselves be raw lower candidates. -/
theorem roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (roughRawCandidateSet n h K)
      (R.paperFixedExceptionalFactors deltaStar) := by
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) (R.paperFixedExceptionalFactors_subset_upperBlock deltaStar)

/-- Actual donors also lie strictly above every raw lower candidate. -/
theorem roughRawCandidateSet_disjoint_prechargeDonorSet
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    Disjoint (roughRawCandidateSet n h K) R.prechargeDonorSet := by
  have hdonor : R.prechargeDonorSet ⊆ roughUpperBlock n h := by
    simpa only [roughUpperBlock, upperEndpoint] using
      R.prechargeDonorSet_subset_tail
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) hdonor

/-- Consequently, the only guard families which can delete a raw lower
coordinate are anchors and the two bank endpoint states.  This is a support
statement, not the still-missing per-row cardinality census. -/
theorem roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
      certificate.anchors ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState := by
  intro a ha
  have haData := Finset.mem_inter.mp ha
  have haRaw := (mem_completeRoughRowFiber.mp haData.1).1
  have haGuard := haData.2
  simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
    Finset.mem_union] at haGuard
  simp only [Finset.mem_union]
  rcases haGuard with (((haAnchor | haFixed) | haDonor) | haBase) | haAlt
  · exact Or.inl (Or.inl haAnchor)
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
        deltaStar)) haRaw haFixed).elim
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_prechargeDonorSet
        (K := K))) haRaw haDonor).elim
  · exact Or.inl (Or.inr haBase)
  · exact Or.inr haAlt

/-! ## Explicit remaining finite/analytic obligations -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardCapacityReduction -/
section


/-!
# Canonical rough-row guard capacity reduction

This file closes the finite part of the three guard-local obligations exposed
by `BankPaperCanonicalGuardLocalRowLedger`.

For every non-smooth complete rough row, at most one central anchor, one bank
base, and one bank alternate can occur.  Thus the literal local guard census
is at most three.  Removing those three possible coordinates from a raw broad
pool gives the guarded-pool capacity, and containment of the guarded broad
pool in the guarded row gives the postcharge capacity.

The only non-finite input left visible is `RoughCanonicalActiveRawBroadSurplus`:
the raw broad pool must contain the larger of the requested pool minimum and
the literal upper-row target, plus the three-coordinate guard slack.  This is
the exact de Bruijn--Saias lower-bound consequence still needed from the
analytic rough-row argument; it contains no selector or bookkeeping premise.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Complete rough labels remember retained prime divisors -/

/-- A prime divisor above the smooth cutoff is retained in the complete
rough label. -/
theorem prime_dvd_completeRoughLabel_of_cutoff_lt
    {y a p : Nat} (hp : p.Prime) (hyp : y < p)
    (ha : a ≠ 0) (hpa : p ∣ a) :
    p ∣ completeRoughLabel y a := by
  apply (hp.dvd_iff_one_le_factorization
    (completeRoughLabel_ne_zero y a)).mpr
  rw [completeRoughLabel_factorization_apply, if_pos hyp]
  exact (hp.dvd_iff_one_le_factorization ha).mp hpa



/-! ## One central anchor in every non-smooth row -/



/-- Consequently, one fixed non-smooth rough row meets the guarded central
anchor set in at most one coordinate. -/
theorem completeRoughRowFiber_inter_guardedCentralAnchors_card_le_one
    {c : Real} {depth n y : Nat} {left right : Nat -> Nat}
    {changed candidates : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyTwo : 2 <= y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (label : Nat) (hlabel : label ≠ 1) :
    (completeRoughRowFiber y candidates label ∩
      certificate.anchors).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have haData := Finset.mem_inter.mp ha
  have hbData := Finset.mem_inter.mp hb
  have haLabel := (mem_completeRoughRowFiber.mp haData.1).2
  have hbLabel := (mem_completeRoughRowFiber.mp hbData.1).2
  apply fullCentralAnchors_completeRoughLabel_injective_of_ne_one
    hnCutoff hyTwo hyCutoff certificate.isCofactorChoice
  · simpa only [certificate.anchors_eq] using haData.2
  · simpa only [certificate.anchors_eq] using hbData.2
  · simpa only [haLabel] using hlabel
  · rw [haLabel, hbLabel]

namespace BankPaperRealization

/-! ## One base and one alternate in every bank row -/

/-- The global bank marker is prime. -/
theorem paperMarker_prime
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    (R.marker request).Prime := by
  cases request with
  | inl request =>
      exact R.bottom.marker_prime
        (bankBottomRelevantRequestToPaperRequest request)
  | inr request => exact R.ordinary.marker_prime request

/-- Every global bank marker lies above the complete rough cutoff. -/
theorem yNat_lt_paperMarker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    yNat n < R.marker request := by
  cases request with
  | inl request =>
      exact R.bottom.yNat_lt_marker R.ordinary.two_mul_n_le_M
        R.three_mul_yNat_le_n
        (bankBottomRelevantRequestToPaperRequest request)
  | inr request => exact R.ordinary.yNat_lt_marker request

/-- The actual donor has the same complete rough signature as its global
marker. -/
theorem prechargeDonor_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n) (R.prechargeDonorValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      simpa only [prechargeDonorValue, marker, fullRequest,
        BankBottomPaperRealization.occurrenceValue_donor] using
        (R.bottom.occurrenceValue_completeRoughSignature R.six_le_yNat
          fullRequest .donor)
  | inr request =>
      have hsignature := completeRoughSignature_marker_mul_smooth_eq
        (y := yNat n) (P := R.ordinary.marker request)
        (a := R.ordinary.donorCore request) (b := 1)
        (R.ordinary.marker_prime request).ne_zero
        (R.ordinary.donorCore_smooth request)
        (by simp [Nat.mem_smoothNumbers])
      simpa only [prechargeDonorValue, marker,
        BankOrdinaryPaperRealization.donorValue, mul_one] using hsignature

theorem prechargeBase_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeBaseStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  exact (R.prechargeBase_donor_completeRoughSignature_eq request).trans
    (R.prechargeDonor_completeRoughSignature_eq_marker request)

theorem prechargeAlternate_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeAlternateStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  exact (R.precharge_completeRoughSignature_eq request).2.trans
    (R.prechargeDonor_completeRoughSignature_eq_marker request)

/-- A prime above the cutoff is its own complete rough label. -/
theorem completeRoughLabel_paperMarker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.marker request) = R.marker request := by
  have hprime := R.paperMarker_prime request
  have hhigh := R.yNat_lt_paperMarker request
  apply Nat.dvd_antisymm
  · exact completeRoughLabel_dvd (yNat n) (R.marker request)
  · exact prime_dvd_completeRoughLabel_of_cutoff_lt hprime hhigh
      hprime.ne_zero (dvd_refl (R.marker request))

theorem prechargeBase_completeRoughLabel_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
      R.marker request := by
  calc
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
        completeRoughLabel (yNat n) (R.marker request) :=
      completeRoughSignature_eq_iff_label_eq.mp
        (R.prechargeBase_completeRoughSignature_eq_marker request)
    _ = R.marker request := R.completeRoughLabel_paperMarker request

theorem prechargeAlternate_completeRoughLabel_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) = R.marker request := by
  calc
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) =
        completeRoughLabel (yNat n) (R.marker request) :=
      completeRoughSignature_eq_iff_label_eq.mp
        (R.prechargeAlternate_completeRoughSignature_eq_marker request)
    _ = R.marker request := R.completeRoughLabel_paperMarker request

theorem prechargeBase_completeRoughLabel_injective
    {n M : Nat} (R : BankPaperRealization n M) :
    Function.Injective (fun request : BankPaperMarkerRequest n =>
      completeRoughLabel (yNat n) (R.prechargeBaseStateValue request)) := by
  intro request request' heq
  apply R.marker_injective
  change
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
      completeRoughLabel (yNat n)
        (R.prechargeBaseStateValue request') at heq
  simpa only [R.prechargeBase_completeRoughLabel_eq_marker] using heq

theorem prechargeAlternate_completeRoughLabel_injective
    {n M : Nat} (R : BankPaperRealization n M) :
    Function.Injective (fun request : BankPaperMarkerRequest n =>
      completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request)) := by
  intro request request' heq
  apply R.marker_injective
  change
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) =
      completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request') at heq
  simpa only [R.prechargeAlternate_completeRoughLabel_eq_marker] using heq

private theorem completeRoughRowFiber_inter_indexedPathState_card_le_one
    {C : Type*} [Fintype C] [DecidableEq C]
    {y label : Nat} {candidates : Finset Nat} (state : C -> Nat)
    (hinjective : Function.Injective
      (fun component => completeRoughLabel y (state component))) :
    (completeRoughRowFiber y candidates label ∩
      indexedPathState state).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have haData := Finset.mem_inter.mp ha
  have hbData := Finset.mem_inter.mp hb
  have haLabel := (mem_completeRoughRowFiber.mp haData.1).2
  have hbLabel := (mem_completeRoughRowFiber.mp hbData.1).2
  rw [indexedPathState, Finset.mem_image] at haData hbData
  obtain ⟨component, _hcomponent, rfl⟩ := haData.2
  obtain ⟨component', _hcomponent', rfl⟩ := hbData.2
  apply congrArg state
  apply hinjective
  change completeRoughLabel y (state component) =
    completeRoughLabel y (state component')
  rw [haLabel, hbLabel]

theorem completeRoughRowFiber_inter_prechargeBaseState_card_le_one
    {n M label : Nat} (R : BankPaperRealization n M)
    (candidates : Finset Nat) :
    (completeRoughRowFiber (yNat n) candidates label ∩
      R.prechargeBaseState).card <= 1 := by
  classical
  rw [prechargeBaseState]
  exact completeRoughRowFiber_inter_indexedPathState_card_le_one
    R.prechargeBaseStateValue
    R.prechargeBase_completeRoughLabel_injective

theorem completeRoughRowFiber_inter_prechargeAlternateState_card_le_one
    {n M label : Nat} (R : BankPaperRealization n M)
    (candidates : Finset Nat) :
    (completeRoughRowFiber (yNat n) candidates label ∩
      R.prechargeAlternateState).card <= 1 := by
  classical
  rw [prechargeAlternateState]
  exact completeRoughRowFiber_inter_indexedPathState_card_le_one
    R.prechargeAlternateStateValue
    R.prechargeAlternate_completeRoughLabel_injective

/-! ## The literal three-coordinate local census -/

/-- In every non-smooth complete rough row, the numerical guards delete at
most one anchor, one bank base, and one bank alternate.  Fixed exceptional
factors and donors are in the upper tail and were already removed by the
support theorem in the local ledger. -/
theorem roughCanonicalGuardLocalCensusBound_three_of_ne_one
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K label : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hlabel : label ≠ 1) :
    RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label 3 := by
  let rawRow := completeRoughRowFiber (yNat n)
    (roughRawCandidateSet n h K) label
  have hsubset :
      R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
        (rawRow ∩ certificate.anchors) ∪
          (rawRow ∩ R.prechargeBaseState) ∪
            (rawRow ∩ R.prechargeAlternateState) := by
    intro a ha
    have haDeleted := ha
    change a ∈ rawRow ∩
      R.roughCanonicalGuardSet certificate deltaStar at haDeleted
    have haRaw : a ∈ rawRow := by
      exact (Finset.mem_inter.mp haDeleted).1
    have haSupport :=
      R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
        certificate deltaStar K label ha
    rcases Finset.mem_union.mp haSupport with haBefore | haAlternate
    · rcases Finset.mem_union.mp haBefore with haAnchor | haBase
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_inter.mpr ⟨haRaw, haAnchor⟩
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_inter.mpr ⟨haRaw, haBase⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_inter.mpr ⟨haRaw, haAlternate⟩
  have hanchor : (rawRow ∩ certificate.anchors).card <= 1 := by
    have hyTwo : 2 <= yNat n := by
      have hySix := R.six_le_yNat
      omega
    exact completeRoughRowFiber_inter_guardedCentralAnchors_card_le_one
      certificate hnCutoff hyTwo hyCutoff label hlabel
  have hbase : (rawRow ∩ R.prechargeBaseState).card <= 1 := by
    exact R.completeRoughRowFiber_inter_prechargeBaseState_card_le_one
      (roughRawCandidateSet n h K)
  have halternate :
      (rawRow ∩ R.prechargeAlternateState).card <= 1 := by
    exact R.completeRoughRowFiber_inter_prechargeAlternateState_card_le_one
      (roughRawCandidateSet n h K)
  have hfirst := Finset.card_union_le
    (rawRow ∩ certificate.anchors) (rawRow ∩ R.prechargeBaseState)
  have hall := Finset.card_union_le
    ((rawRow ∩ certificate.anchors) ∪
      (rawRow ∩ R.prechargeBaseState))
    (rawRow ∩ R.prechargeAlternateState)
  have hcard := Finset.card_le_card hsubset
  exact show
    (R.roughCanonicalGuardDeletedRow certificate deltaStar K label).card <= 3
    by omega

/-- Active nonexceptional rows are non-smooth, so the preceding census
directly supplies the first Section 9 guard-local input. -/
theorem roughCanonicalGuardLocalCensusBound_three_of_active
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K label : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label 3 :=
  R.roughCanonicalGuardLocalCensusBound_three_of_ne_one certificate
    deltaStar K label hnCutoff hyCutoff hactive.1

/-! ## Guarded broad-pool and postcharge capacities -/

/-- A raw pool with `budget` units of surplus retains its requested minimum
after deleting a guard whose intersection with the row has that census. -/
theorem roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K label minimum budget : Nat)
    (hcensus : RoughCanonicalGuardLocalCensusBound R certificate deltaStar
      K label budget)
    (hraw : minimum + budget <=
      (roughCanonicalBroadCorrectionPool W n h K (yNat n) label).card) :
    RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar W K
      label minimum := by
  have hinterSubset :
      roughCanonicalBroadCorrectionPool W n h K (yNat n) label ∩
          R.roughCanonicalGuardSet certificate deltaStar ⊆
        R.roughCanonicalGuardDeletedRow certificate deltaStar K label := by
    intro a ha
    have haData := Finset.mem_inter.mp ha
    exact Finset.mem_inter.mpr
      ⟨roughCanonicalBroadCorrectionPool_subset_rawRow
        W n h K (yNat n) label haData.1, haData.2⟩
  have hinter :
      (roughCanonicalBroadCorrectionPool W n h K (yNat n) label ∩
        R.roughCanonicalGuardSet certificate deltaStar).card <= budget :=
    (Finset.card_le_card hinterSubset).trans hcensus
  unfold RoughCanonicalGuardedBroadPoolCapacity
  rw [roughCanonicalGuardedBroadCorrectionPool, Finset.card_sdiff,
    Finset.inter_comm]
  omega

/-- The postcharge target never exceeds the uncorrected upper-row target. -/
theorem roughCanonicalPostchargeRowTarget_le_upperTarget
    {n h : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) (label : Nat) :
    R.roughCanonicalPostchargeRowTarget deltaStar label <=
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real) := by
  have hfixed : 0 <=
      (completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar) label : Real) := by
    positivity
  have hbase : 0 <=
      (completeLabelMultiplicity (yNat n)
        R.prechargeBaseState label : Real) := by
    positivity
  unfold roughCanonicalPostchargeRowTarget
  linarith

/-- Any guarded broad-pool lower bound at least as large as the literal
upper-row target supplies capacity for the nonnegative postcharge quota. -/
theorem roughCanonicalPostchargeRowCapacity_of_guardedBroadPoolCapacity
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K label minimum : Nat)
    (hupper : roughUpperCompleteRoughRowTarget n h (yNat n) label <= minimum)
    (hpool : RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
      W K label minimum) :
    RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label := by
  have htarget := R.roughCanonicalPostchargeRowTarget_le_upperTarget
    deltaStar label
  have hupperReal :
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real) <=
        (minimum : Real) := by
    exact_mod_cast hupper
  have hpoolRow := Finset.card_le_card
    (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar W K label)
  have hminimumPool : minimum <=
      (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label).card := hpool
  unfold RoughCanonicalPostchargeRowCapacity
  exact htarget.trans <| hupperReal.trans <| by
    exact_mod_cast hminimumPool.trans hpoolRow

/-! ## The single remaining analytic raw-pool input -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic -/
section


/-!
# Eventual raw broad-pool surplus on every active rough row

The tangent clean-list estimate is global in the common multiplier and
therefore cannot by itself give a lower bound in each complete rough row.
The rowwise input needed by the guard-capacity reduction is instead the
`active-clean-pool` estimate from Section 6 of the paper.  This file derives
that estimate from the already proved uniform de Bruijn bound and the
already proved fixed-head endpoint shift.

The proof has three quantitative layers.

* On a fixed-ratio interval `(A,B]`, the Dickman endpoint main term grows by
  a fixed positive multiple of `B-A`.  The uniform friable error is absorbed
  once `log y` is large.
* Exact head Möbius inversion and the fixed-divisor endpoint shift retain a
  fixed multiple of `A` in the head-free smooth interval.
* For an active label, `A = n / label` tends to infinity uniformly, while
  both `label / n` and `upperTailLength c n / n` tend to zero.  Consequently
  the broad pool dominates the literal upper-row quota and the three local
  guards.

The final theorem constructs
`RoughCanonicalActiveRawBroadSurplus ... 3 poolMinimum` for every fixed
`poolMinimum`, without a selector premise or an additional analytic
assumption.  The stronger linear real lower bound used to absorb that
constant is retained separately below.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells
open BankPaperRealization

noncomputable section

/-! ## A positive Dickman floor -/







/-! ## Growth of the unrestricted smooth interval -/





/-! ## Closing the fixed head -/









/-! ## Literal rough-row adapters -/













/-! ## Uniform paper-scale choices -/



















/-- The intrinsic surplus and the literal three-coordinate guard census give
guarded-row capacity before candidate-label attainment is known.  This is
the noncircular coverage input needed when all upper rows are summed. -/
theorem BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
    (W K poolMinimum : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat) (left right : Nat -> Nat)
        (changed : Finset Nat),
      forall (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed),
      centralAnchorCutoffThreshold depth <= n ->
      yNat n < centralAnchorCutoff depth n ->
      forall label, IsCompleteRoughLabel (yNat n) label ->
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalGuardLocalCensusBound R certificate deltaStar K
              label 3 ∧
            RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
              W K label poolMinimum ∧
            RoughCanonicalPostchargeRowCapacity R certificate deltaStar K
              label := by
  filter_upwards [eventually_roughCanonicalActiveIntrinsicRawBroadSurplus
    W K poolMinimum hc hdelta] with n hsurplus
  intro depth left right changed R certificate hnCutoff hyCutoff
    label hlabel hactive
  have hcensus : RoughCanonicalGuardLocalCensusBound R certificate
      deltaStar K label 3 :=
    R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
      deltaStar K label hnCutoff hyCutoff hactive
  have hbroad : RoughCanonicalGuardedBroadPoolCapacity R certificate
      deltaStar W K label poolMinimum := by
    apply R.roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus certificate
      deltaStar W K label poolMinimum 3 hcensus
    exact le_trans
      (Nat.add_le_add_right (Nat.le_max_left _ _) 3)
      (hsurplus label hlabel hactive)
  have hpostcharge : RoughCanonicalPostchargeRowCapacity R certificate
      deltaStar K label := by
    let minimum := max poolMinimum
      (roughUpperCompleteRoughRowTarget n (upperTailLength c n)
        (yNat n) label)
    have hcapacity : RoughCanonicalGuardedBroadPoolCapacity R certificate
        deltaStar W K label minimum := by
      apply R.roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus
        certificate deltaStar W K label minimum 3 hcensus
      exact hsurplus label hlabel hactive
    apply R.roughCanonicalPostchargeRowCapacity_of_guardedBroadPoolCapacity
      certificate deltaStar W K label minimum
    · exact Nat.le_max_right _ _
    · exact hcapacity
  exact ⟨hcensus, hbroad, hpostcharge⟩



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankAnchorCollisionFree -/
section


/-!
# Collision freedom between the complete central anchors and the actual bank

The large-anchor branch recovers the common prime marker from the complete
rough factorization above `yNat`.  Once the marker is recovered, the guarded
central-cofactor certificate excludes the two incident state cores.

The residual branch uses the more rigid shape
`2^k * p^e`.  A bottom marker is already above the residual cutoff.  For an
ordinary marker, divisibility first forces the residual base prime to be the
marker; its marker valuation is then one, so cancellation would make the
ordinary state core a power of two, contrary to the path certificate.

Donor-only occurrences do not create an extra case: ordinary donors and the
two nonterminal bottom donors lie above `2n`, while terminal bottom donors
are literally their upper endpoint state.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## The two eventual scale separations used by marker recovery -/

/-- The elementary square bound behind the separation
`yNat n < centralAnchorCutoff depth n`. -/
theorem bankAnchor_yNat_mul_self_le_self
    {n : ℕ} (hn : 1 ≤ n) : yNat n * yNat n ≤ n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hyFloorNonneg : (0 : ℝ) ≤ yNat n := by positivity
  have hsq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyFloorNonneg hyNonneg).2 hyFloor
  have hpow : (n : ℝ) ^ (4 / 9 : ℝ) ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne
        (by norm_num : (4 / 9 : ℝ) ≤ 1)
  rw [Erdos390.Full.Scale.y_pow_two] at hsq
  have hcast : ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    simpa only [pow_two] using hsq.trans hpow
  exact_mod_cast hcast





/-- At the literal central-anchor threshold, the moving smooth cutoff is
strictly below the residual/large-prime cutoff. -/
theorem yNat_lt_centralAnchorCutoff_of_threshold
    {depth n : ℕ} (hn : 1 ≤ n)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    yNat n < centralAnchorCutoff depth n := by
  have hySq := bankAnchor_yNat_mul_self_le_self hn
  have hcutSq := two_mul_lt_centralAnchorCutoff_sq hnCutoff
  nlinarith

theorem eventually_yNat_lt_centralAnchorCutoff (depth : ℕ) :
    ∀ᶠ n : ℕ in atTop, yNat n < centralAnchorCutoff depth n := by
  filter_upwards [eventually_ge_atTop 1,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth)]
      with n hn hnCutoff
  exact yNat_lt_centralAnchorCutoff_of_threshold hn hnCutoff

/-! ## Arithmetic collision kernels -/



namespace BankPaperRealization



/-! ## Literal recovery of the incident cores from actual requests -/





















/-! ## Complete finite collision theorem -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector -/
section


/-!
# Actual-data connector for the Section 8 analytic ledger

The reduced Section 8 ledger still names the actual post-guard active mass
and the exact frozen mass/logarithmic ledgers.  The Proposition 8.7 actual-
data connector already supplies the finite decomposition needed to make
those objects literal: every guarded candidate is split into its active
seed and its frozen remainder.

This file adjoins the frozen integral factors, defines the resulting exact
total frozen mass and logarithmic contribution, and proves

`m0 + qTilde = #fixed + sum candidates preSelector`

whenever the actual active-measure constructor holds.  Consequently the
first frozen-baseline estimate reduces to the rough selector's literal
total-mass estimate.  For the canonical scaled seed, its active mass is
exactly the guarded smooth base.  Exact interval support then centers the
frozen logarithmic contribution, while the complete central-tail product
satisfies `logY = h * L + O(secondOrderScale)` by elementary factor bounds.
The generic interval-geometry theorem exposes the selector total-mass
estimate, and the final constructed-quota theorem proves that estimate from
the rough-stage frozen baseline ledger, nearest-integer construction, and
the existing `d = O(secondOrderScale / L)` theorem.

No abstract `qTilde`, `m0`, or `Lambda0` remains in the final theorem.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

/-! ## Literal frozen mass and logarithmic contribution -/









/-! ## Families of literal actual data -/





/-! ## Elementary logarithmic geometry of the literal upper tail -/















/-! ## Centering the literal frozen logarithmic ledger -/















/-! ## Exact charged-selector row ledger -/









/-- Expanded exact form of the same identity relative to any raw
pre-selector.  It displays, with signs fixed, all four sources left on the
smooth row: the raw row discrepancy, fixed and precharge-base tokens, the
guard-deleted raw mass, and the later smooth-row mass change. -/
theorem bankPaperCanonical_chargedSelectorMass_sub_height_eq_rawSmoothLedger
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (rawSelector selector : Nat -> Real)
    (hactiveRows : ∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
            selector a) =
          R.roughCanonicalPostchargeRowTarget deltaStar label)
    (hexceptionalRows : ∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      label ≠ 1 -> RoughCanonicalExceptionalLabel n deltaStar label ->
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
            selector a) = 0)
    (hcapacity : forall label, IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label) :
    ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
        (R.prechargeBaseState.card : Real) +
        (∑ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K, selector a) - (h : Real) =
      -roughCanonicalRawRowDiscrepancy n h K 1 rawSelector +
        (completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) 1 : Real) +
        (completeLabelMultiplicity (yNat n) R.prechargeBaseState 1 : Real) -
        (∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
          K 1, rawSelector a) +
        ((∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            selector a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            rawSelector a) := by
  have htotal :=
    bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
      R certificate deltaStar selector hactiveRows hexceptionalRows hcapacity
  have hguard := R.roughCanonicalGuardLocalDiscrepancyLedger
    certificate deltaStar K 1 rawSelector
  rw [BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy]
    at htotal hguard
  linarith

























/-! ## The remaining actual analytic sources -/

















/-! ## Construction of the old Section 8 ledger -/













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



theorem roughBalancedAlphaConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughBalancedAlphaConstant W K0 c beta := by
  unfold roughBalancedAlphaConstant
  have hK : (0 : ℝ) <
      (((K0 + 1 : ℕ) : ℝ)) := by positivity
  have hdelta : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  positivity











/-! ## Quotient and logarithmic geometry -/





























/-! ## The balanced Dickman main ledger -/





/-! ## The weighted sharp Saias transition ledger -/



/-! ## Absorption of the sharp fixed-head divisor sum -/



/-! ## One unified canonical raw-row allowance -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure -/
section


/-!
# Canonical nonsmooth endpoint-slack closure

This module connects the sharp balanced raw-row estimate to the literal
guarded constant-pool correction used at the actual Proposition 8.7
endpoint.

There are two finite guard estimates.  The sharp one assumes the usual
raw-point box and proves that passing through all numerical guards changes
one active row discrepancy by at most `2`.  The assumption-free one uses
the already proved uniform absolute bound for the balanced coefficient and
gives a fixed (slightly larger) numerator constant.  The latter is the
version used in the eventual theorem, so no unproved eventual feasibility
of `roughHeadBalancedAlpha` is hidden in the endpoint-slack conclusion.

The final bounds use the paper split

`beta = betaProt + betaAct`, `0 < betaAct`, `sigma <= betaProt`.

Thus the lower nonsmooth margin has the fixed strict reserve `betaAct/L`.
The upper margin follows once `L` exceeds the fixed sum of the parameters.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.Scale
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Filter Topology
open scoped BigOperators

noncomputable section

namespace BankPaperRealization

/-! ## Active rows contain no fixed exceptional factor -/









/-! ## The sharp finite `+2` guard numerator -/



/-! ## An assumption-free fixed guard numerator -/



theorem roughCanonicalBalancedRawWeightGuardBound_nonneg
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 <= roughCanonicalBalancedRawWeightGuardBound W K0 c beta := by
  unfold roughCanonicalBalancedRawWeightGuardBound
  exact add_nonneg
    (roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc)
    (abs_nonneg beta)

/-- The raw weight is bounded without assuming that the balanced high level
already lies in `[0,1]`. -/
theorem roughHeadCompatibleBalancedRawWeight_abs_le_guardBound
    (W K0 n : Nat) {c beta : Real} (hc : 0 < c)
    (hn : 2 <= n) (hL : 1 <= L n) (a : Nat) :
    |roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
          beta (L n))
        beta (L n) a| <=
      roughCanonicalBalancedRawWeightGuardBound W K0 c beta := by
  let alpha :=
    roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
      beta (L n)
  change
    |roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        alpha beta (L n) a| <=
      roughCanonicalBalancedRawWeightGuardBound W K0 c beta
  have halpha :
      |alpha| <= roughBalancedAlphaConstant W K0 c beta := by
    simpa only [alpha, roughBalancedAlphaConstant] using
      roughHeadBalancedAlpha_succ_abs_le W K0 (beta := beta) hc hn
  have hLPos : 0 < L n := zero_lt_one.trans_le hL
  have hbetaDiv : |beta / L n| <= |beta| := by
    rw [abs_div, abs_of_pos hLPos]
    apply (div_le_iff₀ hLPos).2
    nlinarith [abs_nonneg beta]
  by_cases hcop : Nat.Coprime a (roughHeadModulus W)
  · by_cases hhigh : a ∈
        roughHighLowerBlock n (upperTailLength c n) (K0 + 1)
    · have hbroad : a ∉
          roughBroadLowerBlock n (upperTailLength c n) (K0 + 1) := by
        intro hbroad
        exact Finset.disjoint_left.mp
          (roughHighLowerBlock_disjoint_roughBroadLowerBlock
            n (upperTailLength c n) (K0 + 1)) hhigh hbroad
      have hweight :
          roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
              alpha beta (L n) a = alpha := by
        simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
          hcop, hhigh, hbroad]
      rw [hweight]
      unfold roughCanonicalBalancedRawWeightGuardBound
      exact halpha.trans (le_add_of_nonneg_right (abs_nonneg beta))
    · by_cases hbroad : a ∈
          roughBroadLowerBlock n (upperTailLength c n) (K0 + 1)
      · have hweight :
            roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
                alpha beta (L n) a = beta / L n := by
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            hcop, hhigh, hbroad]
        rw [hweight]
        unfold roughCanonicalBalancedRawWeightGuardBound
        exact hbetaDiv.trans
          (le_add_of_nonneg_left
            (roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc))
      · simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
          hhigh, hbroad,
          roughCanonicalBalancedRawWeightGuardBound_nonneg
            W K0 (beta := beta) hc]
  · simp [roughHeadCompatibleRawWeight, hcop,
      roughCanonicalBalancedRawWeightGuardBound_nonneg
        W K0 (beta := beta) hc]







end BankPaperRealization

/-! ## Eventual sharp raw-row estimate on every active canonical row -/









namespace BankPaperRealization

/-! ## From the raw numerator to the guarded correction density -/











/-! ## The eventual paper beta/sigma nonsmooth bounds -/













end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTopFrozenInitialMassConnector -/
section


/-!
# Initial selector mass from the frozen-top smooth-row bridge

This connector is the asymptotic integration boundary for the separate
`qTilde`-stage source constructed in
`BankPaperCanonicalSectionEightTopFrozenSourceConnector`.

The family-facing premise below is an exact construction equation:
the initial selector has the same guarded label-one row sum as the balanced
literal raw selector.  Together with the existing exact nonsmooth-row state,
the charged row ledger reduces the whole selector-mass error to:

* the balanced raw label-one discrepancy;
* the two charged label-one multiplicities; and
* the balanced raw mass deleted by the numerical guard.

The first term is handled by the sharp Saias row theorem.  Fixed exceptional
factors and bank bases have zero label-one multiplicity in the paper range.
The remaining deleted row is contained in the promoted smooth residual
anchors, hence has cardinality at most `yNat`; the existing uniform balanced
raw-weight bound then absorbs it into `secondOrderScale / L`.

No final-selector quota, height displacement, or Section 9 source state is
used here.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The balanced raw selector used by the initial-mass interface -/



/-! ## The two charged smooth-row multiplicities -/

/-- For `deltaStar <= 1`, no fixed exceptional upper factor can have
complete rough label one: its defining strict inequality would say
`2n < n^deltaStar <= n`. -/
theorem paperFixedExceptionalFactors_completeLabelMultiplicity_one_eq_zero
    {n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : Real} (hn : 0 < n) (hdeltaUpper : deltaStar <= 1) :
    completeLabelMultiplicity (yNat n)
      (R.paperFixedExceptionalFactors deltaStar) 1 = 0 := by
  unfold completeLabelMultiplicity
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro a haFixed haLabel
  have haData := (R.mem_paperFixedExceptionalFactors (a := a)).mp haFixed
  have hexceptional :
      2 * (n : Real) < (n : Real) ^ deltaStar := by
    simpa only [haLabel, Nat.cast_one, div_one] using haData.2.1
  have hnOne : (1 : Real) <= (n : Real) := by
    exact_mod_cast (show 1 <= n by omega)
  have hpower :
      (n : Real) ^ deltaStar <= (n : Real) :=
    Real.rpow_le_self_of_one_le hnOne hdeltaUpper
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  nlinarith

/-- Every precharge base retains its marker prime above `yNat`, so the bank
base state has no complete-label-one coordinate. -/
theorem prechargeBaseState_completeLabelMultiplicity_one_eq_zero
    {n M : Nat} (R : BankPaperRealization n M) :
    completeLabelMultiplicity (yNat n) R.prechargeBaseState 1 = 0 := by
  classical
  unfold completeLabelMultiplicity
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro a haBase haLabel
  rw [BankPaperRealization.prechargeBaseState, indexedPathState,
    Finset.mem_image] at haBase
  obtain ⟨request, _hrequest, rfl⟩ := haBase
  rw [R.prechargeBase_completeRoughLabel_eq_marker] at haLabel
  have hmarker := R.yNat_lt_paperMarker request
  have hy := R.six_le_yNat
  omega

/-! ## Full label-one guard deletion -/

/-- On the full raw label-one row, every deleted coordinate is a central
anchor.  Precharge bases and alternates retain a nontrivial marker label. -/
theorem roughCanonicalGuardDeletedSmoothRow_subset_anchors
    {c : Real} {depth n h K : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) :
    R.roughCanonicalGuardDeletedRow certificate deltaStar K 1 ⊆
      certificate.anchors := by
  classical
  intro a ha
  have haRawRow := (Finset.mem_inter.mp ha).1
  have haSupport :=
    R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
      certificate deltaStar K 1 ha
  rcases Finset.mem_union.mp haSupport with haBefore | haAlternate
  · rcases Finset.mem_union.mp haBefore with haAnchor | haBase
    · exact haAnchor
    · rw [BankPaperRealization.prechargeBaseState, indexedPathState,
        Finset.mem_image] at haBase
      obtain ⟨request, _hrequest, rfl⟩ := haBase
      have hlabel := (mem_completeRoughRowFiber.mp haRawRow).2
      rw [R.prechargeBase_completeRoughLabel_eq_marker] at hlabel
      have hmarker := R.yNat_lt_paperMarker request
      have hy := R.six_le_yNat
      omega
  · rw [BankPaperRealization.prechargeAlternateState, indexedPathState,
      Finset.mem_image] at haAlternate
    obtain ⟨request, _hrequest, rfl⟩ := haAlternate
    have hlabel := (mem_completeRoughRowFiber.mp haRawRow).2
    rw [R.prechargeAlternate_completeRoughLabel_eq_marker] at hlabel
    have hmarker := R.yNat_lt_paperMarker request
    have hy := R.six_le_yNat
    omega

/-- Every central anchor in the full raw label-one row is a promoted
residual anchor whose base prime is at most `yNat`.  This is the full-row
version of the existing broad-base support theorem. -/
theorem guardedCentralAnchors_inter_rawSmoothRow_subset_smoothResidual
    {c : Real} {depth n h K : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    certificate.anchors ∩
        completeRoughRowFiber (yNat n) (roughRawCandidateSet n h K) 1 ⊆
      bankPaperCanonicalSmoothResidualAnchorPool n
        (centralAnchorCutoff depth n) (yNat n) := by
  intro a ha
  have hn : 0 < n :=
    (centralAnchorCutoffThreshold_pos depth).trans_le hnCutoff
  have haRawRow := (Finset.mem_inter.mp ha).2
  have haLabel : completeRoughLabel (yNat n) a = 1 :=
    (mem_completeRoughRowFiber.mp haRawRow).2
  have haAnchor : a ∈ fullCentralAnchors n
      (centralAnchorCutoff depth n) certificate.q := by
    simpa only [certificate.anchors_eq] using
      (Finset.mem_inter.mp ha).1
  rw [fullCentralAnchors] at haAnchor
  rcases Finset.mem_union.mp haAnchor with haPromoted | haLarge
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp haPromoted
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
    by_contra hpNotLe
    have hyp : yNat n < p := Nat.lt_of_not_ge hpNotLe
    have hpPrime := residualCentralPrimes_prime hp
    have hpDvdFactor : p ∣ promotedCentralFactor n p := by
      unfold promotedCentralFactor promotedBlock centralPrimeBlock
      exact dvd_mul_of_dvd_right
        (dvd_pow_self p (residualCentralPrimes_exponent_pos hp).ne') _
    have hpDvdLabel : p ∣
        completeRoughLabel (yNat n) (promotedCentralFactor n p) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hpPrime hyp
        (Nat.zero_lt_of_lt (promotedCentralFactor_gt hn)).ne'
        hpDvdFactor
    rw [haLabel] at hpDvdLabel
    exact hpPrime.not_dvd_one hpDvdLabel
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp haLarge
    have hPPrime := largeCentralPrimes_prime hP
    have hPHigh : yNat n < P :=
      hyCutoff.trans (largeCentralPrimes_gt hP)
    have hPPos : 0 < largeCentralAnchor certificate.q P :=
      Nat.zero_lt_of_lt
        (Finset.mem_Ioc.mp
          (largeCentralAnchor_mem_centralInterval
            certificate.isCofactorChoice hP)).1
    have hPDvdLabel : P ∣
        completeRoughLabel (yNat n)
          (largeCentralAnchor certificate.q P) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
        hPPos.ne' (dvd_mul_right P (certificate.q P))
    rw [haLabel] at hPDvdLabel
    exact (hPPrime.not_dvd_one hPDvdLabel).elim

/-- The full raw label-one deletion set contains at most `yNat n`
coordinates. -/
theorem roughCanonicalGuardDeletedSmoothRow_card_le_yNat
    {c : Real} {depth n h K : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    (R.roughCanonicalGuardDeletedRow certificate deltaStar K 1).card <=
      yNat n := by
  have hsubset :
      R.roughCanonicalGuardDeletedRow certificate deltaStar K 1 ⊆
        certificate.anchors ∩
          completeRoughRowFiber (yNat n)
            (roughRawCandidateSet n h K) 1 := by
    intro a ha
    exact Finset.mem_inter.mpr
      ⟨R.roughCanonicalGuardDeletedSmoothRow_subset_anchors
          certificate deltaStar ha,
        (Finset.mem_inter.mp ha).1⟩
  calc
    (R.roughCanonicalGuardDeletedRow certificate deltaStar K 1).card <=
        (certificate.anchors ∩
          completeRoughRowFiber (yNat n)
            (roughRawCandidateSet n h K) 1).card :=
      Finset.card_le_card hsubset
    _ <=
        (bankPaperCanonicalSmoothResidualAnchorPool n
          (centralAnchorCutoff depth n) (yNat n)).card :=
      Finset.card_le_card
        (guardedCentralAnchors_inter_rawSmoothRow_subset_smoothResidual
          certificate hnCutoff hyCutoff)
    _ <= yNat n :=
      bankPaperCanonicalSmoothResidualAnchorPool_card_le n
        (centralAnchorCutoff depth n) (yNat n)

/-- The deleted balanced raw mass is bounded by the smooth-anchor count
times the existing realization-independent raw-coordinate bound. -/
theorem abs_sum_roughCanonicalGuardDeletedSmoothRow_balancedRawWeight_le
    {c deltaStar beta : Real} {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (hc : 0 < c) (hn : 2 <= n) (hL : 1 <= L n)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    |∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
        (K0 + 1) 1,
      bankPaperCanonicalBalancedRawWeight W K0 c beta n a| <=
      (yNat n : Real) *
        roughCanonicalBalancedRawWeightGuardBound W K0 c beta := by
  let D :=
    R.roughCanonicalGuardDeletedRow certificate deltaStar (K0 + 1) 1
  let M := roughCanonicalBalancedRawWeightGuardBound W K0 c beta
  have hM : 0 <= M := by
    dsimp only [M]
    exact
      roughCanonicalBalancedRawWeightGuardBound_nonneg
        W K0 (beta := beta) hc
  have hcardNat : D.card <= yNat n := by
    dsimp only [D]
    exact R.roughCanonicalGuardDeletedSmoothRow_card_le_yNat
      certificate deltaStar hnCutoff hyCutoff
  have hcardReal : (D.card : Real) <= (yNat n : Real) := by
    exact_mod_cast hcardNat
  calc
    |∑ a ∈ D, bankPaperCanonicalBalancedRawWeight W K0 c beta n a| <=
        ∑ a ∈ D,
          |bankPaperCanonicalBalancedRawWeight W K0 c beta n a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _a ∈ D, M := by
      exact Finset.sum_le_sum fun a _ha => by
        dsimp only [bankPaperCanonicalBalancedRawWeight, M]
        exact roughHeadCompatibleBalancedRawWeight_abs_le_guardBound
          W K0 n (beta := beta) hc hn hL a
    _ = (D.card : Real) * M := by simp
    _ <= (yNat n : Real) * M :=
      mul_le_mul_of_nonneg_right hcardReal hM

/-! ## Paper-scale bounds for the smooth row -/

private theorem topFrozenInitialMass_L_tendsto_atTop :
    Tendsto L atTop atTop := by
  simpa only [L] using
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop



/-- The smooth anchor count is eventually bounded pointwise by the exact
initial-mass error scale `secondOrderScale / L`. -/
theorem eventually_yNat_cast_le_secondOrderScale_div_L :
    ∀ᶠ n : Nat in atTop,
      (yNat n : Real) <= secondOrderScale n / L n := by
  have hratio := tendsto_endpointRatio_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hratio, eventually_ge_atTop 2,
      eventually_bankBottom_six_le_yNat] with n hratioN hn hySix
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < n := by exact_mod_cast hnPos
  have hL : 0 < L n := L_pos hn
  have hyNonneg : 0 <= y n := (y_pos hnPos).le
  have hyFloor : (yNat n : Real) <= y n := Nat.floor_le hyNonneg
  have hySq : (yNat n : Real) ^ 2 <= y n ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hyNonneg).2 hyFloor
  have hratioNat :
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) <= 1 := by
    calc
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) <=
          y n ^ 2 * L n ^ 2 / (n : Real) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hySq (sq_nonneg _)) hnReal.le
      _ = endpointRatio n := by rfl
      _ <= 1 := hratioN.le
  have hySqScale :
      (yNat n : Real) ^ 2 <= (n : Real) / L n ^ 2 := by
    apply (le_div_iff₀ (pow_pos hL 2)).2
    have hcross := (div_le_iff₀ hnReal).1 hratioNat
    simpa only [one_mul] using hcross
  have hyLeSq :
      (yNat n : Real) <= (yNat n : Real) ^ 2 := by
    have hyOne : (1 : Real) <= (yNat n : Real) := by
      exact_mod_cast (show 1 <= yNat n by omega)
    nlinarith [sq_nonneg ((yNat n : Real) - 1)]
  have htarget :
      (n : Real) / L n ^ 2 = secondOrderScale n / L n := by
    unfold secondOrderScale L
    ring
  exact hyLeSq.trans (hySqScale.trans_eq htarget)





/-! ## Exact construction boundary and the charged mass ledger -/



/-- Once the exact smooth-row mass is installed, the charged all-row
identity has only two terms left: the balanced raw discrepancy and the raw
mass removed by the numerical guard. -/
theorem chargedSelectorMass_sub_height_eq_neg_balancedRawDiscrepancy_sub_deleted
    {c deltaStar beta : Real} {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (selector : Nat -> Real)
    (hn : 0 < n) (hdeltaUpper : deltaStar <= 1)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K0 + 1) R certificate deltaStar selector)
    (hcapacity : forall label,
      IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar
          (K0 + 1) label)
    (hsmooth :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar
          (K0 + 1) 1, selector a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar
          (K0 + 1) 1,
            bankPaperCanonicalBalancedRawWeight W K0 c beta n a) :
    ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
        (R.prechargeBaseState.card : Real) +
        (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1), selector a) -
          (upperTailLength c n : Real) =
      -roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n) -
        ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
          (K0 + 1) 1,
            bankPaperCanonicalBalancedRawWeight W K0 c beta n a := by
  have hledger :=
    bankPaperCanonical_chargedSelectorMass_sub_height_eq_rawSmoothLedger
      R certificate deltaStar
        (bankPaperCanonicalBalancedRawWeight W K0 c beta n)
        selector hrows.1 hrows.2 hcapacity
  rw [
    R.paperFixedExceptionalFactors_completeLabelMultiplicity_one_eq_zero
      hn hdeltaUpper,
    R.prechargeBaseState_completeLabelMultiplicity_one_eq_zero,
    hsmooth] at hledger
  simpa only [Nat.cast_zero, add_zero, zero_add, sub_self] using hledger

/-! ## Asymptotic initial-selector mass theorem -/

/-- The frozen-top construction closes the actual initial-selector mass
estimate.

The premise is only an eventual family of exact finite witnesses.  All
analytic inputs—raw quota error, guard capacity, cutoff geometry, and the
size of the deleted smooth row—are discharged internally. -/
theorem bankPaperCanonicalActualSelectorMassEstimate_of_topFrozenBalancedInitial
    (depth W K0 poolMinimum : Nat)
    {c deltaStar beta : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1)
    (fixed bankBase candidates : Nat -> Finset Nat)
    (initialSelector : Nat -> Nat -> Real)
    (Hconstructed : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalTopFrozenBalancedInitialRealization
        depth W K0 n c deltaStar beta
          (fixed n) (bankBase n) (candidates n)
          (initialSelector n)) :
    BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates initialSelector := by
  have Hraw :=
    bankPaperCanonicalBalancedRawSmoothRowDiscrepancy_isBigO
      W K0 hc (beta := beta)
  rcases (isBigO_iff').mp Hraw with
    ⟨Craw, hCraw, HrawBound⟩
  let M := roughCanonicalBalancedRawWeightGuardBound W K0 c beta
  have hM : 0 <= M := by
    dsimp only [M]
    exact
      roughCanonicalBalancedRawWeightGuardBound_nonneg
        W K0 (beta := beta) hc
  have HcapacityRaw :=
    BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
      W (K0 + 1) poolMinimum hc hdelta
  have Hthreshold :=
    eventually_ge_atTop (centralAnchorCutoffThreshold depth)
  have HyCutoff :=
    eventually_yNat_lt_centralAnchorCutoff depth
  have HLOne : ∀ᶠ n : Nat in atTop, 1 <= L n :=
    topFrozenInitialMass_L_tendsto_atTop.eventually
      (eventually_ge_atTop 1)
  unfold BankPaperCanonicalActualSelectorMassEstimate
  apply IsBigO.of_bound (Craw + M)
  filter_upwards [Hconstructed, HrawBound, HcapacityRaw,
      Hthreshold, HyCutoff, eventually_ge_atTop 2, HLOne,
      eventually_yNat_cast_le_secondOrderScale_div_L]
      with n hwitness hrawBoundN hcapacityRaw hnCutoff hyCutoff
        hn hLone hyNatScale
  rcases hwitness with
    ⟨Rn, certn, hfixed, hbankBase, hcandidates, hrows, hsmooth⟩
  have hcapacity :
      forall label, IsCompleteRoughLabel (yNat n) label ->
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalPostchargeRowCapacity Rn certn deltaStar
            (K0 + 1) label := by
    intro label hcomplete hactive
    exact
      (hcapacityRaw depth Rn.anchorGuardLeftCore
        Rn.anchorGuardRightCore (Rn.centralChangedMarkers depth)
        Rn certn hnCutoff hyCutoff label hcomplete hactive).2.2
  have hmass :=
    Rn.chargedSelectorMass_sub_height_eq_neg_balancedRawDiscrepancy_sub_deleted
      certn (initialSelector n) (by omega) hdeltaUpper.le
        hrows hcapacity hsmooth
  have hmassObserved :
      ((fixed n).card : Real) + ((bankBase n).card : Real) +
          (∑ a ∈ candidates n, initialSelector n a) -
            bankPaperCanonicalUpperTailHeight c n =
        -roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
            (K0 + 1) 1
              (bankPaperCanonicalBalancedRawWeight W K0 c beta n) -
          ∑ a ∈ Rn.roughCanonicalGuardDeletedRow certn deltaStar
            (K0 + 1) 1,
              bankPaperCanonicalBalancedRawWeight W K0 c beta n a := by
    simpa only [hfixed, hbankBase, hcandidates,
      bankPaperCanonicalUpperTailHeight] using hmass
  have htargetPos : 0 < secondOrderScale n / L n :=
    div_pos (secondOrderScale_pos (by omega)) (L_pos hn)
  have hrawAbs :
      |roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n)| <=
        Craw * (secondOrderScale n / L n) := by
    simpa only [Real.norm_eq_abs, abs_of_pos htargetPos] using hrawBoundN
  have hdeleted :=
    Rn.abs_sum_roughCanonicalGuardDeletedSmoothRow_balancedRawWeight_le
      certn hc hn hLone hnCutoff hyCutoff
      (deltaStar := deltaStar) (beta := beta) (W := W) (K0 := K0)
  have hdeletedScale :
      |∑ a ∈ Rn.roughCanonicalGuardDeletedRow certn deltaStar
          (K0 + 1) 1,
        bankPaperCanonicalBalancedRawWeight W K0 c beta n a| <=
          (secondOrderScale n / L n) * M := by
    apply hdeleted.trans
    exact mul_le_mul_of_nonneg_right hyNatScale hM
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htargetPos,
    hmassObserved]
  calc
    |-roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n) -
        ∑ a ∈ Rn.roughCanonicalGuardDeletedRow certn deltaStar
          (K0 + 1) 1,
            bankPaperCanonicalBalancedRawWeight W K0 c beta n a| <=
      |-roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n)| +
        |∑ a ∈ Rn.roughCanonicalGuardDeletedRow certn deltaStar
          (K0 + 1) 1,
            bankPaperCanonicalBalancedRawWeight W K0 c beta n a| :=
      abs_sub _ _
    _ = |roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n)| +
        |∑ a ∈ Rn.roughCanonicalGuardDeletedRow certn deltaStar
          (K0 + 1) 1,
            bankPaperCanonicalBalancedRawWeight W K0 c beta n a| := by
      rw [abs_neg]
    _ <= Craw * (secondOrderScale n / L n) +
          (secondOrderScale n / L n) * M :=
      add_le_add hrawAbs hdeletedScale
    _ = (Craw + M) * (secondOrderScale n / L n) := by ring

/-! ## The concrete WithTop/scaled-seed constructor -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal004_009 := by
  exact @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalActualSelectorMassEstimate_of_topFrozenBalancedInitial
