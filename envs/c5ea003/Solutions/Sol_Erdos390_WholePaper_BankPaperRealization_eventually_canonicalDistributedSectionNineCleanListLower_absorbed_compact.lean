-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.eventually_canonicalDistributedSectionNineCleanListLower_absorbed_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.655987+00:00
-- url     : https://prove2.me/submissions/1e41d95d-83a7-4ad4-bfe1-a32a6616d2c8

import Definitions.Def_erdos390_remaining_analytic_propositions_004
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Theorems.Thm_Erdos390_WholePaper_eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses_compact


section
theorem Erdos390.WholePaper.eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses : Erdos390.RemainingAnalyticGoal008_009 := @Erdos390.WholePaper.eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses_compact
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

/- Source module: Erdos390.Full.PrimeSums -/
section


/-!
# Prime sums on the actual moving band

This file derives the finite prime-sum estimates needed in Lemma 7.5 from
Mathlib's Chebyshev bound.  No prime-sum estimate is introduced as a contract.
-/

open scoped BigOperators Nat.Prime
open Filter Topology

namespace Erdos390.Full.PrimeSums

open ArithmeticModel Scale





































private theorem integral_one_div_mul_log {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ t in (2 : ℝ)..Y, 1 / (t * Real.log t)) =
      Real.log (Real.log Y) - Real.log (Real.log 2) := by
  have hint : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t))
      MeasureTheory.volume 2 Y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hY] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.div (continuousAt_id.mul (Real.continuousAt_log ht0))
        (mul_ne_zero ht0 hlog0))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
  intro t ht
  rw [Set.uIcc_of_le hY] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog0 : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have hd := (Real.hasDerivAt_log ht0).log hlog0
  convert hd using 1
  field_simp

/-- An explicit Mertens-type upper bound, obtained from the global Chebyshev
bound by Abel summation.  It is sufficient for every harmonic loss in
Lemma 7.5 and does not invoke the prime number theorem as an assumption. -/
theorem fullReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    fullReciprocalSum Y ≤
      2 * Real.log 4 + 3 * Real.log 4 *
        (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
  rw [fullReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlogYhalf : (1 / 2 : ℝ) ≤ Real.log (Y : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by norm_num) hYR
    nlinarith [Real.log_two_gt_d9]
  have hlogY0 : 0 < Real.log (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hboundary :
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
        2 * Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
          (Real.log 4 * (Y : ℝ)) /
            ((Y : ℝ) * Real.log (Y : ℝ)) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ 2 * Real.log 4 := by
        field_simp [hY0.ne', hlogY0.ne']
        nlinarith
  have hint :
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
        3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
    calc
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
          ∫ t in (2 : ℝ)..Y,
            3 * Real.log 4 * (1 / (t * Real.log t)) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_mertensIntegrand hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          have hlog0 : Real.log t ≠ 0 :=
            Real.log_ne_zero_of_pos_of_ne_one
              (by linarith [ht.1]) (by linarith [ht.1])
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul
              (continuousAt_const.div
                (continuousAt_id.mul (Real.continuousAt_log ht0))
                (mul_ne_zero ht0 hlog0)))
        · intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          have hloghalf : (1 / 2 : ℝ) ≤ Real.log t := by
            have hmono : Real.log 2 ≤ Real.log t :=
              Real.log_le_log (by norm_num) ht.1
            nlinarith [Real.log_two_gt_d9]
          calc
            Chebyshev.theta t * (Real.log t + 1) /
                (t ^ 2 * Real.log t ^ 2) ≤
                (Real.log 4 * t) * (Real.log t + 1) /
                  (t ^ 2 * Real.log t ^ 2) := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (le_of_lt ht0)
            _ ≤ 3 * Real.log 4 * (1 / (t * Real.log t)) := by
              field_simp [ht0.ne', (show Real.log t ≠ 0 by linarith)]
              nlinarith
      _ = 3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_mul_log hYR]
  linarith

/-- A global Chebyshev bound for the logarithmically weighted reciprocal
prime sum.  The deliberately simple constant is uniform in the endpoint. -/
theorem fullLogReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    fullLogReciprocalSum Y ≤ Real.log 4 * (1 + Real.log (Y : ℝ)) := by
  rw [fullLogReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have htheta : Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤ Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤
          (Real.log 4 * (Y : ℝ)) / (Y : ℝ) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = Real.log 4 := by field_simp
  have hint :
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
        Real.log 4 * Real.log (Y : ℝ) := by
    calc
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
          ∫ t in (2 : ℝ)..Y, Real.log 4 * (1 / t) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_theta_div_sq hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul (continuousAt_const.div continuousAt_id ht0))
        · intro t ht
          calc
            Chebyshev.theta t / t ^ 2 ≤ (Real.log 4 * t) / t ^ 2 := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])
            _ = Real.log 4 * (1 / t) := by
              have ht0 : t ≠ 0 := by linarith [ht.1]
              field_simp
      _ = Real.log 4 * Real.log ((Y : ℝ) / 2) := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos (by norm_num) hY0]
      _ ≤ Real.log 4 * Real.log (Y : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hlog4
        apply Real.log_le_log (div_pos hY0 (by norm_num))
        linarith
  nlinarith











end Erdos390.Full.PrimeSums

end

/- Source module: Erdos390.Full.PrimeBandQuadrature -/
section


/-!
# Audited harmonic prime quadrature on moving positive cells

The continuum transfer in Lemma 8.4 uses prime cells whose endpoints are
powers of the smoothness scale.  This file starts the required arithmetic
quadrature from the actual Chebyshev function.  The key identity below has no
Mertens constant: it subtracts Abel summation at two endpoints and isolates
the quantitative PNT remainder exactly.
-/

open scoped BigOperators
open Set
open Filter Topology Asymptotics

noncomputable section

namespace Erdos390.Full.PrimeBandQuadrature

open MeasureTheory
open Erdos390.Full.PrimeSums
open Erdos390.Full.FriableAsymptotic



























/-! ## The first logarithmic moment -/















/-! ## Quantitative PNT remainder -/





















/-! ## Exact alignment with the paper's logarithmic coordinate -/

























theorem fullReciprocalSumUniform_bound
    (A Y : ℕ) (hA : fullReciprocalSumUniformCutoff ≤ A)
    (hAY : A ≤ Y) :
    |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * fullReciprocalSumUniformConstant / Real.log (A : ℝ) ^ 3 :=
  (Classical.choose_spec
    (Classical.choose_spec
      exists_fullReciprocalSum_interval_error_bound).2) A Y hA hAY



end Erdos390.Full.PrimeBandQuadrature

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

/- Source module: Erdos390.WholePaper.CentralAnchorCollision -/
section


/-!
# Collision guards for the three central-anchor families

The prefix and row-zero anchors carry a marker prime above a fixed cutoff.
Every promoted residual factor is supported only at `2` and its base prime,
both below that cutoff.  The lemmas below turn this unique-factorization
observation into literal natural-number noncollision statements.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- A prime divisor of `A_p = 2^k p^e` is either `2` or the base prime
`p`. -/
theorem prime_dvd_promotedCentralFactor
    {n p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hdiv : ℓ ∣ promotedCentralFactor n p) :
    ℓ = 2 ∨ ℓ = p := by
  rw [promotedCentralFactor, promotedBlock, centralPrimeBlock] at hdiv
  rcases hℓ.dvd_mul.mp hdiv with htwo | hpPow
  · left
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
      (hℓ.dvd_of_dvd_pow htwo)
  · right
    exact (Nat.prime_dvd_prime_iff_eq hℓ hp).mp
      (hℓ.dvd_of_dvd_pow hpPow)









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorDivisorSupport -/
section


/-!
# Prime support and valuations of the central-anchor divisor

The exact anchor product introduces only the promotion power of two and the
chosen carry cofactors.  This file makes that assertion literal at every
prime, so later allocation estimates can be applied directly to the actual
integer divisor.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

theorem routedCentralCofactor_pos
    {n p q : ℕ} (hq : IsRoutedCentralCofactor n p q) : 0 < q := by
  rcases hq with hzero | ⟨r, _hrPos, _hr, _hpRow, hqLower, _hqUpper⟩
  · omega
  · omega

theorem largeCentralCofactor_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n X) :
    0 < q p :=
  routedCentralCofactor_pos (hq p hp)











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

/- Source module: Erdos390.WholePaper.FixedModulusReducedResidueCount -/
section


/-!
# Fixed-modulus reduced-residue counts

This file proves the elementary `O_W(1)` input used in the rough selector
and in the tangent-list census.  A reduced-residue predicate is counted on
literal finite intervals by splitting the interval into complete periods
and one remainder.  Multiples of a number coprime to the fixed modulus are
then reindexed exactly by division.

There is no prime-number theorem, smooth-number estimate, or asymptotic
hypothesis in this module.  The final CRT-style error constant is the
explicit number `M + 1`, independent of the multiplier and the interval.
-/

namespace Erdos390.WholePaper

noncomputable section









/-! ## Exact periodic decomposition -/

/-- Splitting a segment after `first` tokens splits the finite set itself. -/
theorem reducedResidueSegment_add
    (M start first second : ℕ) :
    reducedResidueSegment M start (first + second) =
      reducedResidueSegment M start first ∪
        reducedResidueSegment M (start + first) second := by
  ext a
  simp only [reducedResidueSegment, Finset.mem_filter,
    Finset.mem_Ico, Finset.mem_union]
  omega

/-- The two pieces in `reducedResidueSegment_add` are disjoint. -/
theorem reducedResidueSegment_disjoint
    (M start first second : ℕ) :
    Disjoint (reducedResidueSegment M start first)
      (reducedResidueSegment M (start + first) second) := by
  rw [Finset.disjoint_left]
  intro a haFirst haSecond
  simp only [reducedResidueSegment, Finset.mem_filter,
    Finset.mem_Ico] at haFirst haSecond
  omega

/-- Cardinalities add under the literal segment split. -/
theorem reducedResidueSegment_card_add
    (M start first second : ℕ) :
    (reducedResidueSegment M start (first + second)).card =
      (reducedResidueSegment M start first).card +
        (reducedResidueSegment M (start + first) second).card := by
  rw [reducedResidueSegment_add,
    Finset.card_union_of_disjoint
      (reducedResidueSegment_disjoint M start first second)]

/-- Every complete interval of length `M` contains exactly `phi(M)`
reduced residues, regardless of its starting point. -/
theorem reducedResidueSegment_card_period
    (M start : ℕ) :
    (reducedResidueSegment M start M).card = M.totient := by
  simpa only [reducedResidueSegment, Nat.coprime_comm] using
    Nat.filter_coprime_Ico_eq_totient M start

/-- `q` complete periods contain exactly `q * phi(M)` reduced residues. -/
theorem reducedResidueSegment_card_fullBlocks
    (M start q : ℕ) :
    (reducedResidueSegment M start (q * M)).card =
      q * M.totient := by
  induction q generalizing start with
  | zero => simp [reducedResidueSegment]
  | succ q ih =>
      calc
        (reducedResidueSegment M start ((q + 1) * M)).card =
            (reducedResidueSegment M start (q * M)).card +
              (reducedResidueSegment M (start + q * M) M).card := by
          rw [Nat.succ_mul, reducedResidueSegment_card_add]
        _ = q * M.totient + M.totient := by
          rw [ih, reducedResidueSegment_card_period]
        _ = (q + 1) * M.totient := by ring

/-- Exact quotient-and-remainder formula for every finite segment. -/
theorem reducedResidueSegment_card_eq_fullBlocks_add_remainder
    (M start length : ℕ) :
    (reducedResidueSegment M start length).card =
      (length / M) * M.totient +
        (reducedResidueSegment M
          (start + (length / M) * M) (length % M)).card := by
  have hlength :
      length = (length / M) * M + length % M := by
    calc
      length = length % M + M * (length / M) :=
        (Nat.mod_add_div length M).symm
      _ = (length / M) * M + length % M := by ac_rfl
  calc
    (reducedResidueSegment M start length).card =
        (reducedResidueSegment M start
          ((length / M) * M + length % M)).card :=
      congrArg (fun segmentLength ↦
        (reducedResidueSegment M start segmentLength).card) hlength
    _ = (reducedResidueSegment M start ((length / M) * M)).card +
        (reducedResidueSegment M
          (start + (length / M) * M) (length % M)).card :=
      reducedResidueSegment_card_add M start
        ((length / M) * M) (length % M)
    _ = (length / M) * M.totient +
        (reducedResidueSegment M
          (start + (length / M) * M) (length % M)).card := by
      rw [reducedResidueSegment_card_fullBlocks]

/-- A filtered segment contains at most its literal number of tokens. -/
theorem reducedResidueSegment_card_le_length
    (M start length : ℕ) :
    (reducedResidueSegment M start length).card ≤ length := by
  unfold reducedResidueSegment
  calc
    ((Finset.Ico start (start + length)).filter
        (fun a ↦ Nat.Coprime a M)).card ≤
      (Finset.Ico start (start + length)).card :=
        Finset.card_filter_le _ _
    _ = length := by simp

/-- A physical `(lo,hi]` interval is literally the corresponding shifted
half-open segment. -/
theorem reducedResidueIoc_eq_segment
    {M lo hi : ℕ} (hlohi : lo ≤ hi) :
    reducedResidueIoc M lo hi =
      reducedResidueSegment M (lo + 1) (hi - lo) := by
  ext a
  simp only [reducedResidueIoc, reducedResidueSegment,
    Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-! ## Explicit fixed-period error -/

/-- The exact endpoint error is bounded by the length of the incomplete
period, not merely by an unspecified modulus-dependent constant. -/
theorem reducedResidueSegment_card_error_le_mod
    {M : ℕ} (hM : 0 < M) (start length : ℕ) :
    |((reducedResidueSegment M start length).card : ℝ) -
        fixedModulusReducedResidueDensity M * (length : ℝ)| ≤
      ((length % M : ℕ) : ℝ) := by
  let q := length / M
  let r := length % M
  let remainderCard :=
    (reducedResidueSegment M (start + q * M) r).card
  have hcount :
      (reducedResidueSegment M start length).card =
        q * M.totient + remainderCard := by
    simpa only [q, r, remainderCard] using
      reducedResidueSegment_card_eq_fullBlocks_add_remainder
        M start length
  have hlength : length = q * M + r := by
    dsimp only [q, r]
    calc
      length = length % M + M * (length / M) :=
        (Nat.mod_add_div length M).symm
      _ = (length / M) * M + length % M := by ac_rfl
  have hremainderLeNat : remainderCard ≤ r := by
    dsimp only [remainderCard]
    exact reducedResidueSegment_card_le_length M (start + q * M) r
  have hremainderLe : (remainderCard : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast hremainderLeNat
  have hMRealPos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hM
  have hMReal : (M : ℝ) ≠ 0 := hMRealPos.ne'
  have htotientLe : (M.totient : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Nat.totient_le M
  have hdensityNonneg :
      0 ≤ fixedModulusReducedResidueDensity M := by
    exact div_nonneg (Nat.cast_nonneg _) hMRealPos.le
  have hdensityLeOne :
      fixedModulusReducedResidueDensity M ≤ 1 := by
    rw [fixedModulusReducedResidueDensity]
    exact (div_le_one hMRealPos).2 htotientLe
  have hmainNonneg :
      0 ≤ fixedModulusReducedResidueDensity M * (r : ℝ) :=
    mul_nonneg hdensityNonneg (Nat.cast_nonneg _)
  have hmainLe :
      fixedModulusReducedResidueDensity M * (r : ℝ) ≤ (r : ℝ) := by
    calc
      fixedModulusReducedResidueDensity M * (r : ℝ) ≤
          1 * (r : ℝ) :=
        mul_le_mul_of_nonneg_right hdensityLeOne (Nat.cast_nonneg _)
      _ = (r : ℝ) := one_mul _
  have herror :
      ((reducedResidueSegment M start length).card : ℝ) -
          fixedModulusReducedResidueDensity M * (length : ℝ) =
        (remainderCard : ℝ) -
          fixedModulusReducedResidueDensity M * (r : ℝ) := by
    rw [hcount, hlength]
    simp only [fixedModulusReducedResidueDensity, Nat.cast_add,
      Nat.cast_mul]
    field_simp [hMReal]
    ring
  have hremainderNonneg : (0 : ℝ) ≤ (remainderCard : ℝ) := by
    exact Nat.cast_nonneg remainderCard
  rw [herror, abs_le]
  constructor <;> linarith

/-- Physical-interval form of the exact remainder bound. -/
theorem reducedResidueIoc_card_error_le_mod
    {M lo hi : ℕ} (hM : 0 < M) (hlohi : lo ≤ hi) :
    |((reducedResidueIoc M lo hi).card : ℝ) -
        fixedModulusReducedResidueDensity M * ((hi - lo : ℕ) : ℝ)| ≤
      (((hi - lo) % M : ℕ) : ℝ) := by
  rw [reducedResidueIoc_eq_segment hlohi]
  exact reducedResidueSegment_card_error_le_mod hM (lo + 1) (hi - lo)

/-- Coarser but convenient `O_M(1)` form with the explicit constant `M`. -/
theorem reducedResidueIoc_card_error_le_modulus
    {M lo hi : ℕ} (hM : 0 < M) (hlohi : lo ≤ hi) :
    |((reducedResidueIoc M lo hi).card : ℝ) -
        fixedModulusReducedResidueDensity M * ((hi - lo : ℕ) : ℝ)| ≤
      (M : ℝ) := by
  exact (reducedResidueIoc_card_error_le_mod hM hlohi).trans
    (by exact_mod_cast (Nat.mod_lt (hi - lo) hM).le)

/-! ## Exact CRT reindexing and multiplier-independent error -/

/-- Multiplication by `D` gives an exact bijection between coprime
multiples in `(lo,hi]` and reduced residues in `(lo/D,hi/D]`. -/
theorem coprimeMultipleIoc_card_eq_reducedResidueIoc
    {M D lo hi : ℕ} (hD : 0 < D) (hDM : Nat.Coprime D M) :
    (coprimeMultipleIoc M D lo hi).card =
      (reducedResidueIoc M (lo / D) (hi / D)).card := by
  apply Finset.card_bij (fun a _ha ↦ a / D)
  · intro a ha
    simp only [coprimeMultipleIoc, Finset.mem_filter,
      Finset.mem_Ioc] at ha
    obtain ⟨haInterval, hDvd, hcoprime⟩ := ha
    simp only [reducedResidueIoc, Finset.mem_filter,
      Finset.mem_Ioc]
    refine ⟨⟨(Nat.div_lt_iff_lt_mul hD).mpr ?_,
      (Nat.le_div_iff_mul_le hD).mpr ?_⟩, ?_⟩
    · simpa [Nat.div_mul_cancel hDvd] using haInterval.1
    · simpa [Nat.div_mul_cancel hDvd] using haInterval.2
    · rw [← Nat.div_mul_cancel hDvd] at hcoprime
      exact (Nat.coprime_mul_iff_left.mp hcoprime).1
  · intro a₁ ha₁ a₂ ha₂ heq
    simp only [coprimeMultipleIoc, Finset.mem_filter,
      Finset.mem_Ioc] at ha₁ ha₂
    calc
      a₁ = a₁ / D * D := (Nat.div_mul_cancel ha₁.2.1).symm
      _ = a₂ / D * D := by rw [heq]
      _ = a₂ := Nat.div_mul_cancel ha₂.2.1
  · intro b hb
    simp only [reducedResidueIoc, Finset.mem_filter,
      Finset.mem_Ioc] at hb
    refine ⟨b * D, ?_, ?_⟩
    · simp only [coprimeMultipleIoc, Finset.mem_filter,
        Finset.mem_Ioc]
      refine ⟨⟨(Nat.div_lt_iff_lt_mul hD).mp hb.1.1,
        (Nat.le_div_iff_mul_le hD).mp hb.1.2⟩, by simp, ?_⟩
      exact Nat.coprime_mul_iff_left.mpr ⟨hb.2, hDM⟩
    · exact Nat.mul_div_left b hD

/-- Integer quotient lengths differ from real division by less than one.
This is the only extra endpoint cost after the exact multiplication
reindexing. -/
theorem quotientIocLength_sub_realLengthDiv_abs_lt_one
    {D lo hi : ℕ} (hD : 0 < D) (hlohi : lo ≤ hi) :
    |(((hi / D - lo / D : ℕ) : ℝ)) -
        ((hi - lo : ℕ) : ℝ) / (D : ℝ)| < 1 := by
  have hquotient : lo / D ≤ hi / D := Nat.div_le_div_right hlohi
  have hDRealPos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast hD
  have hDReal : (D : ℝ) ≠ 0 := hDRealPos.ne'
  have hhi := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div hi D)
  have hlo := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div lo D)
  simp only [Nat.cast_add, Nat.cast_mul] at hhi hlo
  have herror :
      (((hi / D - lo / D : ℕ) : ℝ)) -
          ((hi - lo : ℕ) : ℝ) / (D : ℝ) =
        ((lo % D : ℕ) : ℝ) / (D : ℝ) -
          ((hi % D : ℕ) : ℝ) / (D : ℝ) := by
    rw [Nat.cast_sub hquotient, Nat.cast_sub hlohi]
    field_simp [hDReal]
    nlinarith [hhi, hlo]
  have hloMod : ((lo % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt lo hD
  have hhiMod : ((hi % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt hi hD
  have hloModNonneg :
      0 ≤ ((lo % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  have hhiModNonneg :
      0 ≤ ((hi % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  rw [herror, abs_lt]
  constructor <;> linarith



/-! ## Paper-head specializations -/









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

/-- Product recovery in the opposite orientation. -/
theorem completeRoughLabel_mul_completeSmoothPart (y a : ℕ) :
    completeRoughLabel y a * completeSmoothPart y a = a :=
  (completeRough_decomposition y a).symm

/-! ## The complementary low-prime factorization -/





/-- Nonzero high-part coordinates lie strictly above the cutoff. -/
theorem completeRoughLabel_factorization_support
    {y a p : ℕ}
    (hp : (completeRoughLabel y a).factorization p ≠ 0) :
    y < p := by
  rw [completeRoughLabel_factorization_apply] at hp
  by_contra hpHigh
  simp [hpHigh] at hp



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

theorem card_bankBottomPaperRequests (n : ℕ) :
    (bankBottomPaperRequests n).card = 8 * bankBottomPaperDemand n := by
  have hsigned :
      Fintype.card (SignedBankSlot (bankRoundingBetaOnSupport n)) =
        2 * bankBottomPaperDemand n := by
    rw [Fintype.card_sigma]
    change (∑ p : bankRoundingPrimeSupport n,
      Fintype.card (Fin (bankRoundingBeta n p) ⊕ Fin (bankRoundingBeta n p))) = _
    simp only [Fintype.card_sum, Fintype.card_fin]
    calc
      (∑ p : ↑(bankRoundingPrimeSupport n),
          (bankRoundingBeta n p.1 + bankRoundingBeta n p.1)) =
          2 * ∑ p : ↑(bankRoundingPrimeSupport n),
            bankRoundingBeta n p.1 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _hp
              omega
      _ = 2 * bankBottomPaperDemand n := by
        congr 1
        simpa only [bankBottomPaperDemand] using
          (Finset.sum_attach (bankRoundingPrimeSupport n)
            (fun p ↦ bankRoundingBeta n p))
  rw [bankBottomPaperRequests, Finset.card_univ, Fintype.card_prod,
    hsigned, show Fintype.card BankBottomMove = 4 by decide]
  ring





/-! ## Eventual local geometry and the terminal realized family -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankGeometricDescentCore -/
section


/-!
# Literal finite algebra for the large-core bank descent

This module contains only the discrete ceiling, power-of-two avoidance, and
exact inequalities used by the geometric descent in Section 5.  It has no
donor-counting or prime-distribution input.
-/

namespace Erdos390.WholePaper

noncomputable section













































/-- Two exact `17/20` contractions starting below `4Q/3` finish below `Q`.
This is the arithmetic heart of the at-most-two-edges-per-large-cell claim. -/
theorem two_seventeen_twentieth_steps_below_cell
    {Q : ℚ} {q₀ q₁ q₂ : ℕ}
    (hQ : 20 < Q) (hq₀ : (q₀ : ℚ) ≤ 4 * Q / 3)
    (h₀₁ : 20 * q₁ < 17 * q₀)
    (h₁₂ : 20 * q₂ < 17 * q₁) :
    (q₂ : ℚ) < Q := by
  have hcomp : 400 * q₂ < 289 * q₀ := by omega
  have hcompQ : (400 : ℚ) * q₂ < 289 * q₀ := by
    exact_mod_cast hcomp
  linarith

/-- If the first target remains in the same large cell, the second target
has already crossed below that cell. -/
theorem two_consecutive_largeCoreSteps_leave_cell
    {Q : ℚ} {q : ℕ} (hQ : 20 < Q)
    (hsource : CoreInGeometricCell Q q)
    (hfirst : CoreInGeometricCell Q (largeCoreStep q)) :
    ((largeCoreStep (largeCoreStep q) : ℕ) : ℚ) < Q := by
  have hq20Q : (20 : ℚ) < q := hQ.trans hsource.1
  have hfirst20Q : (20 : ℚ) < largeCoreStep q := hQ.trans hfirst.1
  have hq21 : 21 ≤ q := by
    have : 20 < q := by exact_mod_cast hq20Q
    omega
  have hfirst21 : 21 ≤ largeCoreStep q := by
    have : 20 < largeCoreStep q := by exact_mod_cast hfirst20Q
    omega
  exact two_seventeen_twentieth_steps_below_cell hQ hsource.2
    (largeCoreStep_cross_seventeen hq21)
    (largeCoreStep_cross_seventeen hfirst21)

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryCorePaths -/
section


/-!
# Actual terminating ordinary-bank core paths

This file turns the large-core rule and the certified fifteen-row small table
into one deterministic finite path.  Sources `6,...,22` use the displayed
table, sources above `22` use `largeCoreStep`, and `5` is absorbing.  The
resulting finite source set is the literal set of ordinary component requests
made by one path.

The rational geometric grid is indexed here as well.  Minimality of the index
puts every source in its unique grid cell.  The finite small part contributes
at most seventeen sources at any scale, while the two-step contraction gives
the sharp bound two at every grid scale above the small table.
-/

namespace Erdos390.WholePaper

open scoped BigOperators

noncomputable section

/-! ## One deterministic descent step -/

















/-! ## Exact indexing of the rational geometric grid -/



















theorem twentyTwo_lt_bankOrdinaryScale_of_six_le
    {j : ℕ} (hj : 6 ≤ j) :
    (22 : ℚ) < bankOrdinaryScale j := by
  have hscale := bankOrdinaryScale_mono hj
  norm_num [bankOrdinaryScale] at hscale ⊢
  linarith

/-! ## The scale and certificate carried by every component -/







theorem smallDescentScaleIndex_le_five (scale : SmallDescentScale) :
    smallDescentScaleIndex scale ≤ 5 := by
  cases scale <;> decide











/-! ## A literal finite terminating path -/



























/-! ## The actual finite path telescopes -/













/-- Indices at or below the small table can only label literal small-table
sources. -/
theorem bankOrdinaryComponentSource_le_twentyTwo_of_scaleIndex_le_five
    {q : ℕ} (_hq : 6 ≤ q)
    (hindex : bankOrdinaryComponentScaleIndex q ≤ 5) :
    q ≤ 22 := by
  by_contra hq22
  have hq23 : 23 ≤ q := by omega
  have hge := bankOrdinaryScaleIndex_ge_six hq23
  rw [bankOrdinaryComponentScaleIndex, if_neg (by omega : ¬q ≤ 22)]
      at hindex
  omega







private theorem bankOrdinaryCoreSources_in_largeCell_card_le_two
    {q j : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q)
    (hj : 6 ≤ j) :
    ((bankOrdinaryCoreSources q).filter fun s ↦
        CoreInGeometricCell (bankOrdinaryScale j) s).card ≤ 2 := by
  classical
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq5 : q ≤ 5
      · rw [bankOrdinaryCoreSources_of_le_five hq5]
        simp
      · have hq6 : 6 ≤ q := by omega
        let b := bankOrdinaryCoreStep q
        have hspec := bankOrdinaryCoreStep_spec hq6 hqPower
        have hb5 : 5 ≤ b := hspec.2.2.2.1
        have hbLt : b < q := hspec.2.2.2.2.1
        have hbPower : ¬ IsPowerOfTwo b := hspec.2.2.1
        have hQ20 := twenty_lt_bankOrdinaryScale_of_six_le hj
        by_cases hqLow : (q : ℚ) ≤ bankOrdinaryScale j
        · have hempty :
              (bankOrdinaryCoreSources q).filter (fun s ↦
                CoreInGeometricCell (bankOrdinaryScale j) s) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro s hs hcell
            have hsle := bankOrdinaryCoreSource_le_start hs
            have hsleQ : (s : ℚ) ≤ q := by exact_mod_cast hsle
            exact (not_lt_of_ge (hsleQ.trans hqLow)) hcell.1
          rw [hempty]
          simp
        · by_cases hqUpper :
              (q : ℚ) ≤ 4 * bankOrdinaryScale j / 3
          · have hqCell : CoreInGeometricCell (bankOrdinaryScale j) q :=
              ⟨lt_of_not_ge hqLow, hqUpper⟩
            by_cases hbLow : (b : ℚ) ≤ bankOrdinaryScale j
            · have hsubset :
                  (bankOrdinaryCoreSources q).filter (fun s ↦
                      CoreInGeometricCell (bankOrdinaryScale j) s) ⊆
                    {q} := by
                intro s hs
                have hsSource := (Finset.mem_filter.mp hs).1
                rw [bankOrdinaryCoreSources_of_six_le hq6] at hsSource
                rcases Finset.mem_insert.mp hsSource with rfl | hsTail
                · simp
                · have hsle := bankOrdinaryCoreSource_le_start hsTail
                  have hsleQ : (s : ℚ) ≤ b := by exact_mod_cast hsle
                  exact False.elim ((not_lt_of_ge (hsleQ.trans hbLow))
                    (Finset.mem_filter.mp hs).2.1)
              calc
                ((bankOrdinaryCoreSources q).filter fun s ↦
                    CoreInGeometricCell (bankOrdinaryScale j) s).card ≤
                    ({q} : Finset ℕ).card := Finset.card_le_card hsubset
                _ = 1 := Finset.card_singleton q
                _ ≤ 2 := by norm_num
            · have hbCell : CoreInGeometricCell (bankOrdinaryScale j) b := by
                refine ⟨lt_of_not_ge hbLow, ?_⟩
                have hbq : (b : ℚ) < q := by exact_mod_cast hbLt
                exact hbq.le.trans hqUpper
              have hQ22 := twentyTwo_lt_bankOrdinaryScale_of_six_le hj
              have hq22 : 22 < q := by
                have : (22 : ℚ) < q := hQ22.trans hqCell.1
                exact_mod_cast this
              have hb22 : 22 < b := by
                have : (22 : ℚ) < b := hQ22.trans hbCell.1
                exact_mod_cast this
              have hqLarge := bankOrdinaryCoreStep_eq_largeCoreStep hq22
              have hbLarge := bankOrdinaryCoreStep_eq_largeCoreStep hb22
              have hleave := two_consecutive_largeCoreSteps_leave_cell
                hQ20 hqCell (by simpa only [b, hqLarge] using hbCell)
              have hleave' :
                  ((bankOrdinaryCoreStep b : ℕ) : ℚ) <
                    bankOrdinaryScale j := by
                rw [hbLarge]
                simpa only [b, hqLarge] using hleave
              have hsubset :
                  (bankOrdinaryCoreSources q).filter (fun s ↦
                      CoreInGeometricCell (bankOrdinaryScale j) s) ⊆
                    {q, b} := by
                intro s hs
                have hsSource := (Finset.mem_filter.mp hs).1
                rw [bankOrdinaryCoreSources_of_six_le hq6] at hsSource
                rcases Finset.mem_insert.mp hsSource with rfl | hsTail
                · simp
                · rw [bankOrdinaryCoreSources_of_six_le (by omega : 6 ≤ b)]
                      at hsTail
                  rcases Finset.mem_insert.mp hsTail with rfl | hsAfter
                  · simp
                  · have hsle := bankOrdinaryCoreSource_le_start hsAfter
                    have hsleQ : (s : ℚ) ≤ bankOrdinaryCoreStep b := by
                      exact_mod_cast hsle
                    exact False.elim ((not_lt_of_ge hsleQ)
                      (hleave'.trans (Finset.mem_filter.mp hs).2.1))
              calc
                ((bankOrdinaryCoreSources q).filter fun s ↦
                    CoreInGeometricCell (bankOrdinaryScale j) s).card ≤
                    ({q, b} : Finset ℕ).card := Finset.card_le_card hsubset
                _ ≤ 2 := Finset.card_le_two
          · have hqNotCell :
                ¬ CoreInGeometricCell (bankOrdinaryScale j) q := by
              intro hcell
              exact hqUpper hcell.2
            have htail := ih b hbLt hb5 hbPower
            rw [bankOrdinaryCoreSources_of_six_le hq6,
              Finset.filter_insert, if_neg hqNotCell]
            simpa only [b] using htail

/-- Sharp per-path congestion at a large grid scale: at most two actual
ordinary components of a path use that scale. -/
theorem bankOrdinaryCoreSourcesAtLargeScale_card_le_two
    {q j : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q)
    (hj : 6 ≤ j) :
    (bankOrdinaryCoreSourcesAtScale q j).card ≤ 2 := by
  classical
  have hsubset : bankOrdinaryCoreSourcesAtScale q j ⊆
      (bankOrdinaryCoreSources q).filter (fun s ↦
        CoreInGeometricCell (bankOrdinaryScale j) s) := by
    intro s hs
    have hsData := Finset.mem_filter.mp hs
    have hspec := bankOrdinaryCoreSource_spec hq hqPower hsData.1
    apply Finset.mem_filter.mpr
    refine ⟨hsData.1, ?_⟩
    rw [← hsData.2]
    exact hspec.2.2.2.2.2.2.1
  exact (Finset.card_le_card hsubset).trans
    (bankOrdinaryCoreSources_in_largeCell_card_le_two hq hqPower hj)

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























/-- A prime above `n/(R+1)` has quotient row at most `R`. -/
theorem div_le_fixedPrefix_of_centralAnchorCutoff_lt
    {R n p : ℕ} (hp : centralAnchorCutoff R n < p) :
    n / p ≤ R := by
  have hpPos : 0 < p := by omega
  have hdiv : n / (R + 1) < p := by
    simpa only [centralAnchorCutoff] using hp
  have hnUpper : n < p * (R + 1) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < R + 1)).1 hdiv
  have hrow : n / p < R + 1 :=
    (Nat.div_lt_iff_lt_mul hpPos).2 (by
      simpa only [Nat.mul_comm] using hnUpper)
  omega

theorem largeCentralPrime_div_le_fixedPrefix
    {R n p : ℕ}
    (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    n / p ≤ R :=
  div_le_fixedPrefix_of_centralAnchorCutoff_lt
    (largeCentralPrimes_gt hp)



/-- Every routed cofactor above the literal cutoff is in the fixed
cofactor prefix `[1,2R+1]`. -/
theorem largeCentralCofactor_le_fixedPrefix
    {R n : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    q p ≤ 2 * R + 1 := by
  rcases hq p hp with hzero |
      ⟨r, _hrPos, hr, _hpRow, _hqLower, hqUpper⟩
  · omega
  · have hrUpper : r ≤ R := by
      rw [hr]
      exact largeCentralPrime_div_le_fixedPrefix hp
    omega





















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















theorem prechargeAlternateStateValue_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.prechargeAlternateStateValue := by
  intro request request' heq
  by_contra hrequest
  exact R.prechargeEndpointValue_ne_of_request_ne
    hrequest .alternate .alternate heq





/-! ## Literal finite states, donor tail, and replacement map -/













theorem prechargeBaseState_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseState.card =
      Fintype.card (BankPaperMarkerRequest n) := by
  rw [prechargeBaseState, indexedPathState,
    Finset.card_image_of_injective _ R.prechargeBaseStateValue_injective]
  simp

theorem prechargeAlternateState_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeAlternateState.card =
      Fintype.card (BankPaperMarkerRequest n) := by
  rw [prechargeAlternateState, indexedPathState,
    Finset.card_image_of_injective _
      R.prechargeAlternateStateValue_injective]
  simp









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



theorem card_bankPaperMarkerRequest (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) =
      (bankBottomRelevantPaperRequests n).card +
        (bankOrdinaryPaperRequests n).card := by
  change Fintype.card
      (↑(bankBottomRelevantPaperRequests n) ⊕
        ↑(bankOrdinaryPaperRequests n)) = _
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]



















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCommonMultiplierLists -/
section


/-!
# Finite common-multiplier lists for the tangent absorber

This file begins the literal common-list construction of Section 9.  It
defines the integer interval

`(n / v, (2 * n - K * h) / u]`

and applies exactly the five tests appearing in the paper: head
coprimality, the exceptional-row cutoff, exclusion of dedicated rows, and
the two numerical endpoint guards.  The resulting list is finite by
construction.

The uniform positive-density lower bound still needs the paper's reduced
residue-class count and exceptional-row Selberg-sieve estimate.  Everything
around those two analytic inputs is proved here: endpoint location, the
complete-rough-row identity, the exact finite deletion ledger, and the
paper's combinatorial fact that an exhaustive guard set deletes at most two
multipliers per guard.
-/

namespace Erdos390.WholePaper

noncomputable section

/-! ## Literal interval and cleanliness predicates -/



























/-! ## Endpoint location and complete rough rows -/

/-- Membership in `I_uv`, together with `0<v≤u`, puts both numerical
endpoints in the broad interval `(n,2n-Kh]`. -/
theorem tangentCommonMultiplierInterval_endpoints
    {n K h u v a : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u)
    (ha : a ∈ tangentCommonMultiplierInterval n K h u v) :
    u * a ∈ Finset.Ioc n (tangentBroadUpper n K h) ∧
      v * a ∈ Finset.Ioc n (tangentBroadUpper n K h) := by
  have haBounds := mem_tangentCommonMultiplierInterval.mp ha
  have hvLower : n < v * a := by
    have h := (Nat.div_lt_iff_lt_mul hv).mp haBounds.1
    simpa only [Nat.mul_comm] using h
  have huLower : n < u * a := by
    exact hvLower.trans_le (Nat.mul_le_mul_right a hvu)
  have huUpper : u * a ≤ tangentBroadUpper n K h := by
    have h := (Nat.le_div_iff_mul_le hu).mp haBounds.2
    simpa only [Nat.mul_comm] using h
  have hvUpper : v * a ≤ tangentBroadUpper n K h :=
    (Nat.mul_le_mul_right a hvu).trans huUpper
  exact ⟨Finset.mem_Ioc.mpr ⟨huLower, huUpper⟩,
    Finset.mem_Ioc.mpr ⟨hvLower, hvUpper⟩⟩







/-! ## Exact finite deletion counts -/

/-- For a nonzero label, each numerical guard deletes at most one
multiplier.  This is the injectivity argument `a=g/label` used in the paper. -/
theorem card_tangentLabelGuardDeletedMultipliers_le
    {label : ℕ} (hlabel : 0 < label)
    (numericalGuards multipliers : Finset ℕ) :
    (tangentLabelGuardDeletedMultipliers
      label numericalGuards multipliers).card ≤
        numericalGuards.card := by
  classical
  let deleted := tangentLabelGuardDeletedMultipliers
    label numericalGuards multipliers
  have hmulInjective : Function.Injective (fun a : ℕ ↦ label * a) := by
    intro a b hab
    exact mul_left_cancel₀ hlabel.ne' hab
  calc
    deleted.card = (deleted.image (fun a : ℕ ↦ label * a)).card :=
      (Finset.card_image_of_injective deleted hmulInjective).symm
    _ ≤ numericalGuards.card := by
      apply Finset.card_le_card
      intro endpoint hendpoint
      obtain ⟨a, ha, hvalue⟩ := Finset.mem_image.mp hendpoint
      rw [← hvalue]
      exact (Finset.mem_filter.mp ha).2

/-- The two endpoints of a common pair therefore delete at most twice the
size of the exhaustive numerical guard set. -/
theorem card_tangentEndpointGuardDeletedMultipliers_le
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (numericalGuards multipliers : Finset ℕ) :
    (tangentEndpointGuardDeletedMultipliers
      u v numericalGuards multipliers).card ≤
        2 * numericalGuards.card := by
  rw [tangentEndpointGuardDeletedMultipliers]
  calc
    (tangentLabelGuardDeletedMultipliers
          u numericalGuards multipliers ∪
        tangentLabelGuardDeletedMultipliers
          v numericalGuards multipliers).card ≤
        (tangentLabelGuardDeletedMultipliers
          u numericalGuards multipliers).card +
        (tangentLabelGuardDeletedMultipliers
          v numericalGuards multipliers).card :=
      Finset.card_union_le _ _
    _ ≤ numericalGuards.card + numericalGuards.card :=
      Nat.add_le_add
        (card_tangentLabelGuardDeletedMultipliers_le
          hu numericalGuards multipliers)
        (card_tangentLabelGuardDeletedMultipliers_le
          hv numericalGuards multipliers)
    _ = 2 * numericalGuards.card := by omega

/-- Every declared bad class is a subset of the raw interval. -/
theorem tangentCommonMultiplierBadSet_subset_interval
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    tangentCommonMultiplierBadSet
        n K h Phead X0 y u v dedicatedRows numericalGuards ⊆
      tangentCommonMultiplierInterval n K h u v := by
  unfold tangentCommonMultiplierBadSet
    tangentHeadBadMultipliers tangentExceptionalMultipliers
    tangentDedicatedRowMultipliers
    tangentEndpointGuardDeletedMultipliers
    tangentLabelGuardDeletedMultipliers
  exact Finset.union_subset
    (Finset.union_subset
      (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (Finset.filter_subset _ _))
    (Finset.union_subset
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))

/-- The direct clean-list filter is exactly the raw interval minus the union
of the four bad classes. -/
theorem tangentCleanCommonMultiplierList_eq_sdiff_badSet
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards =
      tangentCommonMultiplierInterval n K h u v \
        tangentCommonMultiplierBadSet
          n K h Phead X0 y u v dedicatedRows numericalGuards := by
  classical
  ext a
  by_cases ha : a ∈ tangentCommonMultiplierInterval n K h u v
  · simp [tangentCleanCommonMultiplierList,
      tangentCommonMultiplierBadSet, tangentHeadBadMultipliers,
      tangentExceptionalMultipliers, tangentDedicatedRowMultipliers,
      tangentEndpointGuardDeletedMultipliers,
      tangentLabelGuardDeletedMultipliers, ha, not_lt]
  · simp [tangentCleanCommonMultiplierList,
      tangentCommonMultiplierBadSet, tangentHeadBadMultipliers,
      tangentExceptionalMultipliers, tangentDedicatedRowMultipliers,
      tangentEndpointGuardDeletedMultipliers,
      tangentLabelGuardDeletedMultipliers, ha]



/-- Union bound for the four bad classes before inserting any analytic
estimate for the head or exceptional loss. -/
theorem card_tangentCommonMultiplierBadSet_le
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    (tangentCommonMultiplierBadSet
      n K h Phead X0 y u v dedicatedRows numericalGuards).card ≤
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentDedicatedRowMultipliers y dedicatedRows
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentEndpointGuardDeletedMultipliers u v numericalGuards
        (tangentCommonMultiplierInterval n K h u v)).card := by
  rw [tangentCommonMultiplierBadSet]
  have hHeadExceptional := Finset.card_union_le
    (tangentHeadBadMultipliers Phead
      (tangentCommonMultiplierInterval n K h u v))
    (tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v))
  have hDedicated := Finset.card_union_le
    (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v) ∪
      tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v))
    (tangentDedicatedRowMultipliers y dedicatedRows
      (tangentCommonMultiplierInterval n K h u v))
  have hGuard := Finset.card_union_le
    (tangentHeadBadMultipliers Phead
          (tangentCommonMultiplierInterval n K h u v) ∪
        tangentExceptionalMultipliers n X0 y
          (tangentCommonMultiplierInterval n K h u v) ∪
        tangentDedicatedRowMultipliers y dedicatedRows
          (tangentCommonMultiplierInterval n K h u v))
    (tangentEndpointGuardDeletedMultipliers u v numericalGuards
      (tangentCommonMultiplierInterval n K h u v))
  omega



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentPaperNumericalGuards -/
section


/-!
# The literal Section 9 numerical guards and bank-row census

This file instantiates the exhaustive numerical guard family used by the
tangent common lists.  In the notation of the paper it is exactly

`Γ_num = H' ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Here `H'` is the actual guarded central-anchor set, `G_fix` is supplied by
the eventual rough selector, and the last three sets are the already
constructed precharge donor, base-state, and alternate-state sets.  The
global union is bounded directly from these definitions.  For a permitted
pair `u,v`, its lower-endpoint-relevant subfamily has at most two promoted
anchors and two bank states per component; fixed exceptional factors and
donors disappear because they lie strictly above `2n`.

The paper's bank-row census is also made literal.  The nontrivial bank rows
are the realized marker rows, while the fully dedicated set is empty.  Thus
the dedicated-row deletion in `TangentCommonMultiplierLists` is exactly
zero, without an assumed cardinality estimate.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Actual bank rows and the exhaustive five-family guard set -/





















end BankPaperRealization

/-! ## Only promoted anchors can meet a permitted medium label -/

/-- A prime between the fixed cofactor prefix and the smooth cutoff cannot
divide any routed large-marker anchor. -/
theorem mediumPrime_not_dvd_guardedLargeCentralAnchor
    {c : ℝ} {depth n W y ℓ P : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hPrefix : 2 * depth + 1 ≤ W)
    (hWℓ : W < ℓ) (hℓy : ℓ ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (hℓPrime : ℓ.Prime)
    (hP : P ∈ largeCentralPrimes n
      (centralAnchorCutoff depth n)) :
    ¬ℓ ∣ largeCentralAnchor certificate.q P := by
  intro hdiv
  rw [largeCentralAnchor] at hdiv
  rcases hℓPrime.dvd_mul.mp hdiv with hℓP | hℓq
  · have hPPrime := largeCentralPrimes_prime hP
    have hEq : ℓ = P :=
      (Nat.prime_dvd_prime_iff_eq hℓPrime hPPrime).mp hℓP
    have hPLarge := largeCentralPrimes_gt hP
    omega
  · have hqPos : 0 < certificate.q P :=
      largeCentralCofactor_pos certificate.isCofactorChoice hP
    have hℓLeQ : ℓ ≤ certificate.q P := Nat.le_of_dvd hqPos hℓq
    have hqLe : certificate.q P ≤ 2 * depth + 1 :=
      largeCentralCofactor_le_fixedPrefix
        certificate.isCofactorChoice hP
    omega

/-- For one permitted pair, every central anchor divisible by `u` or `v`
is one of the two corresponding promoted factors.  The prefix, row-zero,
and other large-marker anchors are eliminated arithmetically. -/
theorem guardedCentralAnchors_pairPrimeDivisors_subset
    {c : ℝ} {depth n W y u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g) ⊆
      {promotedCentralFactor n u, promotedCentralFactor n v} := by
  intro g hg
  have hgAnchor := (Finset.mem_filter.mp hg).1
  have hgDiv := (Finset.mem_filter.mp hg).2
  rw [certificate.anchors_eq, fullCentralAnchors] at hgAnchor
  rcases Finset.mem_union.mp hgAnchor with hgPromoted | hgLarge
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hgPromoted
    have hpPrime := residualCentralPrimes_prime hp
    rcases hgDiv with huDiv | hvDiv
    · rcases prime_dvd_promotedCentralFactor hpPrime huPrime huDiv with
        huTwo | hup
      · omega
      · subst p
        simp
    · rcases prime_dvd_promotedCentralFactor hpPrime hvPrime hvDiv with
        hvTwo | hvp
      · omega
      · subst p
        simp
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hgLarge
    exfalso
    rcases hgDiv with huDiv | hvDiv
    · exact mediumPrime_not_dvd_guardedLargeCentralAnchor
        certificate hPrefix (hWv.trans_le hvu) huy hyCutoff
          huPrime hP huDiv
    · exact mediumPrime_not_dvd_guardedLargeCentralAnchor
        certificate hPrefix hWv (hvu.trans huy) hyCutoff
          hvPrime hP hvDiv

theorem card_guardedCentralAnchors_pairPrimeDivisors_le_two
    {c : ℝ} {depth n W y u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g)).card ≤ 2 := by
  have hsubset := guardedCentralAnchors_pairPrimeDivisors_subset
    certificate hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime
  have hcard := Finset.card_le_card hsubset
  have hpair :
      ({promotedCentralFactor n u,
          promotedCentralFactor n v} : Finset ℕ).card ≤ 2 := by
    exact Finset.card_le_two
  omega

namespace BankPaperRealization

/-! ## A lossless endpoint-relevant overapproximation and its upper bound -/



theorem tangentPaperPairNumericalGuards_subset_anchor_states
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M) :
    R.tangentPaperPairNumericalGuards certificate fixedExceptional
        K h u v ⊆
      certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g) ∪
        R.prechargeBaseState ∪ R.prechargeAlternateState := by
  intro g hg
  have hgData := Finset.mem_filter.mp hg
  have hgGuard := hgData.1
  have hgUpper := hgData.2.1
  have hgDiv := hgData.2.2
  simp only [tangentPaperNumericalGuardSet, Finset.mem_union] at hgGuard
  rcases hgGuard with hgBeforeAlternate | hgAlternate
  · rcases hgBeforeAlternate with hgBeforeBase | hgBase
    · rcases hgBeforeBase with hgBeforeDonor | hgDonor
      · rcases hgBeforeDonor with hgAnchor | hgFixed
        · exact Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_union.mpr <| Or.inl <|
              Finset.mem_filter.mpr ⟨hgAnchor, hgDiv⟩
        · have htail := Finset.mem_Ioc.mp (hfixedTail hgFixed)
          have hbroad : tangentBroadUpper n K h ≤ 2 * n := by
            exact Nat.sub_le _ _
          omega
      · have htail := Finset.mem_Ioc.mp
          (R.prechargeDonorSet_subset_tail hgDonor)
        have hbroad : tangentBroadUpper n K h ≤ 2 * n := by
          exact Nat.sub_le _ _
        omega
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inr hgBase
  · exact Finset.mem_union.mpr <| Or.inr hgAlternate

theorem tangentPaperPairNumericalGuards_card_le_componentCount
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v).card ≤
        2 + 2 * Fintype.card (BankPaperMarkerRequest n) := by
  let anchorGuards :=
    certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g)
  have hsubset := R.tangentPaperPairNumericalGuards_subset_anchor_states
    (K := K) (h := h) (u := u) (v := v)
      certificate fixedExceptional hfixedTail
  change R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v ⊆ anchorGuards ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState at hsubset
  have hAnchor : anchorGuards.card ≤ 2 := by
    simpa only [anchorGuards] using
      card_guardedCentralAnchors_pairPrimeDivisors_le_two
        certificate hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime
  have hAnchorBase := Finset.card_union_le
    anchorGuards R.prechargeBaseState
  have hAlternate := Finset.card_union_le
    (anchorGuards ∪ R.prechargeBaseState) R.prechargeAlternateState
  have htarget :
      (anchorGuards ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState).card ≤
          anchorGuards.card + R.prechargeBaseState.card +
            R.prechargeAlternateState.card := by
    omega
  have hPairCard := Finset.card_le_card hsubset
  rw [R.prechargeBaseState_card, R.prechargeAlternateState_card] at htarget
  omega



/-! ## Filtering is lossless for actual endpoint deletion -/

theorem tangentLabelGuardDeletedMultipliers_numericalGuardSet_eq_pair_left
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    tangentLabelGuardDeletedMultipliers u
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
        (tangentCommonMultiplierInterval n K h u v) =
      tangentLabelGuardDeletedMultipliers u
        (R.tangentPaperPairNumericalGuards certificate fixedExceptional
          K h u v)
        (tangentCommonMultiplierInterval n K h u v) := by
  ext a
  simp only [tangentLabelGuardDeletedMultipliers, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hguard⟩
    refine ⟨ha, ?_⟩
    rw [tangentPaperPairNumericalGuards, Finset.mem_filter]
    have hendpoints := tangentCommonMultiplierInterval_endpoints
      hu hv hvu ha
    exact ⟨hguard, (Finset.mem_Ioc.mp hendpoints.1).2,
      Or.inl (dvd_mul_right u a)⟩
  · rintro ⟨ha, hguard⟩
    rw [tangentPaperPairNumericalGuards, Finset.mem_filter] at hguard
    exact ⟨ha, hguard.1⟩

theorem tangentLabelGuardDeletedMultipliers_numericalGuardSet_eq_pair_right
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    tangentLabelGuardDeletedMultipliers v
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
        (tangentCommonMultiplierInterval n K h u v) =
      tangentLabelGuardDeletedMultipliers v
        (R.tangentPaperPairNumericalGuards certificate fixedExceptional
          K h u v)
        (tangentCommonMultiplierInterval n K h u v) := by
  ext a
  simp only [tangentLabelGuardDeletedMultipliers, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hguard⟩
    refine ⟨ha, ?_⟩
    rw [tangentPaperPairNumericalGuards, Finset.mem_filter]
    have hendpoints := tangentCommonMultiplierInterval_endpoints
      hu hv hvu ha
    exact ⟨hguard, (Finset.mem_Ioc.mp hendpoints.2).2,
      Or.inr (dvd_mul_right v a)⟩
  · rintro ⟨ha, hguard⟩
    rw [tangentPaperPairNumericalGuards, Finset.mem_filter] at hguard
    exact ⟨ha, hguard.1⟩

theorem tangentEndpointGuardDeletedMultipliers_numericalGuardSet_eq_pair
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    tangentEndpointGuardDeletedMultipliers u v
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
        (tangentCommonMultiplierInterval n K h u v) =
      tangentEndpointGuardDeletedMultipliers u v
        (R.tangentPaperPairNumericalGuards certificate fixedExceptional
          K h u v)
        (tangentCommonMultiplierInterval n K h u v) := by
  unfold tangentEndpointGuardDeletedMultipliers
  rw [R.tangentLabelGuardDeletedMultipliers_numericalGuardSet_eq_pair_left
      certificate fixedExceptional hu hv hvu,
    R.tangentLabelGuardDeletedMultipliers_numericalGuardSet_eq_pair_right
      certificate fixedExceptional hu hv hvu]

/-- The actual five-family guard set deletes at most four multipliers plus
four per precharged bank component for a permitted pair. -/
theorem card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (tangentEndpointGuardDeletedMultipliers u v
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
      (tangentCommonMultiplierInterval n K h u v)).card ≤
        4 + 4 * Fintype.card (BankPaperMarkerRequest n) := by
  rw [R.tangentEndpointGuardDeletedMultipliers_numericalGuardSet_eq_pair
    certificate fixedExceptional huPrime.pos hvPrime.pos hvu]
  have hguard := card_tangentEndpointGuardDeletedMultipliers_le
    huPrime.pos hvPrime.pos
    (R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v)
    (tangentCommonMultiplierInterval n K h u v)
  have hpair := R.tangentPaperPairNumericalGuards_card_le_componentCount
    (W := W) (K := K) (h := h) (u := u) (v := v)
      certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
        hyCutoff huPrime hvPrime
  omega



/-! ## The actual deterministic common-list ledger -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperSharpCensus -/
section


/-!
# Sharp census for the actual paper bank

The earlier all-marker budget bounded one ordinary core path by its starting
prime and consequently gave `O(yNat²)`.  The constructed path is much
shorter.  Its sources are routed through the literal geometric grid
`Q_j=4(4/3)^j`; every grid fiber has bounded congestion, and only
logarithmically many indices occur below `yNat`.

This file counts the actual sigma-type request family.  It first records the
exact weighted path ledger

`|ordinary requests| = 2 ∑_{p≤y} β_p |coreSources(p)|`,

then bounds every path by an explicit logarithmic grid budget.  Combining
this finite count with the already proved `O(yNat)` beta demand gives the
paper-sized `O(yNat * L)` marker budget.  The only prime-counting input is
the existing audited theorem `bankBottomPaperDemand_isBigO_yNat`, whose
proof uses the safe PNT; no new counting hypothesis is introduced here.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Exact ordinary request ledger -/



/-- The actual dependent request type has exactly two signed copies of the
weighted path ledger. -/
theorem card_bankOrdinaryPaperRequests_eq_weightedPathDemand (n : ℕ) :
    (bankOrdinaryPaperRequests n).card =
      2 * bankOrdinaryWeightedPathDemand n := by
  rw [bankOrdinaryPaperRequests, Finset.card_univ,
    Fintype.card_sigma, bankOrdinaryWeightedPathDemand]
  simp only [Fintype.card_coe]
  change
    (∑ slot : SignedBankSlot (bankRoundingBetaOnSupport n),
      (bankOrdinaryCoreSources slot.1.1).card) =
        2 * ∑ p ∈ bankRoundingPrimeSupport n,
          bankRoundingBeta n p * (bankOrdinaryCoreSources p).card
  simp only [Fintype.sum_sigma, Fintype.card_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, bankRoundingBetaOnSupport]
  have hattach :
      (∑ p : ↑(bankRoundingPrimeSupport n),
        bankRoundingBeta n p.1 *
          (bankOrdinaryCoreSources p.1).card) =
        ∑ p ∈ bankRoundingPrimeSupport n,
          bankRoundingBeta n p *
            (bankOrdinaryCoreSources p).card := by
    simpa only using
      (Finset.sum_attach (bankRoundingPrimeSupport n)
        (fun p ↦ bankRoundingBeta n p *
          (bankOrdinaryCoreSources p).card))
  rw [← hattach, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  change Fintype.card (Fin (bankRoundingBeta n p) ⊕ Fin (bankRoundingBeta n p)) *
    (bankOrdinaryCoreSources p).card = _
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring_nf

/-! ## A literal logarithmic path budget -/

/-- Monotonicity of the least geometric-grid index, in the range in which
the grid-cell certificate has its strict lower endpoint. -/
theorem bankOrdinaryScaleIndex_mono_of_five_le
    {a b : ℕ} (ha : 5 ≤ a) (hab : a ≤ b) :
    bankOrdinaryScaleIndex a ≤ bankOrdinaryScaleIndex b := by
  have hb : 5 ≤ b := ha.trans hab
  have haCell := bankOrdinaryScaleIndex_cell ha
  have hbCell := bankOrdinaryScaleIndex_cell hb
  by_contra hindex
  have hsucc : bankOrdinaryScaleIndex b + 1 ≤
      bankOrdinaryScaleIndex a := by omega
  have hscaleMono := bankOrdinaryScale_mono hsucc
  have hbUpper : (b : ℚ) ≤
      bankOrdinaryScale (bankOrdinaryScaleIndex b + 1) := by
    have hupper := hbCell.2
    rw [← bankOrdinaryScale_succ] at hupper
    exact hupper
  have habQ : (a : ℚ) ≤ b := by exact_mod_cast hab
  have haUpper : (a : ℚ) ≤
      bankOrdinaryScale (bankOrdinaryScaleIndex a) :=
    habQ.trans (hbUpper.trans hscaleMono)
  exact (not_lt_of_ge haUpper) haCell.1





/-- A source routed above the small table has grid index no larger than the
index of `yNat`.  This is where monotonicity of the *actual* constructed
path, rather than the coarse bound by its starting prime, enters. -/
theorem bankOrdinaryComponentScaleIndex_le_yNatScaleIndex_of_six_le
    {n p s : ℕ} (hp : p ∈ bankRoundingPrimeSupport n)
    (hs : s ∈ bankOrdinaryCoreSources p)
    (hscale : 6 ≤ bankOrdinaryComponentScaleIndex s) :
    bankOrdinaryComponentScaleIndex s ≤
      bankOrdinaryScaleIndex (yNat n) := by
  have hpPrime := bankRoundingPrimeSupport_prime hp
  have hpFive : 5 ≤ p := by
    by_contra hpSmall
    have hpLe : p ≤ 5 := by omega
    rw [bankOrdinaryCoreSources_of_le_five hpLe] at hs
    simp at hs
  have hpPower : ¬ IsPowerOfTwo p :=
    prime_not_isPowerOfTwo_of_five_le hpPrime hpFive
  have hspec := bankOrdinaryCoreSource_spec hpFive hpPower hs
  have hsSix : 6 ≤ s := hspec.1
  have hsLarge : ¬ s ≤ 22 := by
    intro hsSmall
    rw [bankOrdinaryComponentScaleIndex, if_pos hsSmall] at hscale
    have hsmall := smallDescentScaleIndex_le_five
      (smallDescentScaleForSource s)
    omega
  have hsStart := bankOrdinaryCoreSource_le_start hs
  have hpY := bankRoundingPrimeSupport_le_yNat hp
  have hsY : s ≤ yNat n := hsStart.trans hpY
  rw [bankOrdinaryComponentScaleIndex, if_neg hsLarge]
  exact bankOrdinaryScaleIndex_mono_of_five_le
    (show 5 ≤ s by omega) hsY

/-- Every actual source is either in the one finite small-table block, or
in one of the explicitly enumerated large grid fibers.  This is the finite
injection/counting reduction behind the sharp census. -/
theorem bankOrdinaryCoreSources_subset_smallLargePathFibers
    {n p : ℕ} (hp : p ∈ bankRoundingPrimeSupport n) :
    bankOrdinaryCoreSources p ⊆
      (bankOrdinaryCoreSources p).filter
          (fun s ↦ bankOrdinaryComponentScaleIndex s ≤ 5) ∪
        (Finset.Icc 6 (bankOrdinaryScaleIndex (yNat n))).biUnion
          (bankOrdinaryCoreSourcesAtScale p) := by
  intro s hs
  apply Finset.mem_union.mpr
  by_cases hscale : bankOrdinaryComponentScaleIndex s ≤ 5
  · exact Or.inl (Finset.mem_filter.mpr ⟨hs, hscale⟩)
  · apply Or.inr
    apply Finset.mem_biUnion.mpr
    refine ⟨bankOrdinaryComponentScaleIndex s, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega,
        bankOrdinaryComponentScaleIndex_le_yNatScaleIndex_of_six_le
          hp hs (by omega)⟩
    · exact Finset.mem_filter.mpr ⟨hs, rfl⟩

/-- The actual deterministic path of every supported prime has at most the
literal logarithmic budget above. -/
theorem bankOrdinaryCoreSources_card_le_pathComponentBudget
    {n p : ℕ} (hp : p ∈ bankRoundingPrimeSupport n) :
    (bankOrdinaryCoreSources p).card ≤
      bankOrdinaryPathComponentBudget n := by
  by_cases hpSmall : p ≤ 5
  · rw [bankOrdinaryCoreSources_of_le_five hpSmall]
    simp [bankOrdinaryPathComponentBudget]
  · have hpPrime := bankRoundingPrimeSupport_prime hp
    have hpFive : 5 ≤ p := by omega
    have hpPower : ¬ IsPowerOfTwo p :=
      prime_not_isPowerOfTwo_of_five_le hpPrime hpFive
    let smallSources := (bankOrdinaryCoreSources p).filter
      (fun s ↦ bankOrdinaryComponentScaleIndex s ≤ 5)
    let largeIndices :=
      Finset.Icc 6 (bankOrdinaryScaleIndex (yNat n))
    let largeSources := largeIndices.biUnion
      (bankOrdinaryCoreSourcesAtScale p)
    have hcover := bankOrdinaryCoreSources_subset_smallLargePathFibers hp
    change bankOrdinaryCoreSources p ⊆
      smallSources ∪ largeSources at hcover
    have hsmallSubset : smallSources ⊆ Finset.Icc 6 22 := by
      intro s hs
      have hsData := Finset.mem_filter.mp hs
      have hspec := bankOrdinaryCoreSource_spec hpFive hpPower hsData.1
      exact Finset.mem_Icc.mpr ⟨hspec.1,
        bankOrdinaryComponentSource_le_twentyTwo_of_scaleIndex_le_five
          hspec.1 hsData.2⟩
    have hsmallCard : smallSources.card ≤ 17 := by
      exact (Finset.card_le_card hsmallSubset).trans (by norm_num)
    have hlargeFiber : ∀ j ∈ largeIndices,
        (bankOrdinaryCoreSourcesAtScale p j).card ≤ 2 := by
      intro j hj
      exact bankOrdinaryCoreSourcesAtLargeScale_card_le_two
        hpFive hpPower (Finset.mem_Icc.mp hj).1
    have hlargeIndexCard : largeIndices.card =
        bankOrdinaryScaleIndex (yNat n) - 5 := by
      dsimp only [largeIndices]
      rw [Nat.card_Icc]
      omega
    have hlargeCard : largeSources.card ≤
        2 * (bankOrdinaryScaleIndex (yNat n) - 5) := by
      calc
        largeSources.card ≤ ∑ j ∈ largeIndices,
            (bankOrdinaryCoreSourcesAtScale p j).card := by
          dsimp only [largeSources]
          exact Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ largeIndices, 2 := by
          exact Finset.sum_le_sum hlargeFiber
        _ = 2 * (bankOrdinaryScaleIndex (yNat n) - 5) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id,
            hlargeIndexCard]
          ring_nf
    calc
      (bankOrdinaryCoreSources p).card ≤
          (smallSources ∪ largeSources).card := by
        exact Finset.card_le_card hcover
      _ ≤ smallSources.card + largeSources.card :=
        Finset.card_union_le _ _
      _ ≤ 17 + 2 * (bankOrdinaryScaleIndex (yNat n) - 5) :=
        Nat.add_le_add hsmallCard hlargeCard
      _ = bankOrdinaryPathComponentBudget n := rfl

theorem bankOrdinaryWeightedPathDemand_le
    (n : ℕ) :
    bankOrdinaryWeightedPathDemand n ≤
      bankBottomPaperDemand n * bankOrdinaryPathComponentBudget n := by
  rw [bankOrdinaryWeightedPathDemand, bankBottomPaperDemand]
  calc
    (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p * (bankOrdinaryCoreSources p).card) ≤
      ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p * bankOrdinaryPathComponentBudget n := by
          apply Finset.sum_le_sum
          intro p hp
          exact Nat.mul_le_mul_left _
            (bankOrdinaryCoreSources_card_le_pathComponentBudget hp)
    _ = (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p) * bankOrdinaryPathComponentBudget n := by
          rw [Finset.sum_mul]

theorem card_bankOrdinaryPaperRequests_le_sharp
    (n : ℕ) :
    (bankOrdinaryPaperRequests n).card ≤
      2 * bankBottomPaperDemand n *
        bankOrdinaryPathComponentBudget n := by
  rw [card_bankOrdinaryPaperRequests_eq_weightedPathDemand]
  have hweighted := bankOrdinaryWeightedPathDemand_le n
  calc
    2 * bankOrdinaryWeightedPathDemand n ≤
        2 * (bankBottomPaperDemand n *
          bankOrdinaryPathComponentBudget n) :=
      Nat.mul_le_mul_left 2 hweighted
    _ = 2 * bankBottomPaperDemand n *
        bankOrdinaryPathComponentBudget n := by ring

/-! ## The full actual marker/component census -/





theorem card_bankPaperMarkerRequest_le_sharpMarkerBudget
    (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperSharpMarkerBudget n := by
  have hbottom : (bankBottomRelevantPaperRequests n).card ≤
      8 * bankBottomPaperDemand n := by
    calc
      (bankBottomRelevantPaperRequests n).card ≤
          (bankBottomPaperRequests n).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 8 * bankBottomPaperDemand n :=
        card_bankBottomPaperRequests n
  have hordinary := card_bankOrdinaryPaperRequests_le_sharp n
  rw [BankPaperRealization.card_bankPaperMarkerRequest,
    bankPaperSharpMarkerBudget]
  calc
    (bankBottomRelevantPaperRequests n).card +
          (bankOrdinaryPaperRequests n).card ≤
        8 * bankBottomPaperDemand n +
          2 * bankBottomPaperDemand n *
            bankOrdinaryPathComponentBudget n :=
      Nat.add_le_add hbottom hordinary
    _ = bankBottomPaperDemand n *
        (2 * bankOrdinaryPathComponentBudget n + 8) := by ring

namespace BankPaperRealization

theorem prechargeComponentCount_le_sharpMarkerBudget
    {n M : ℕ} (_R : BankPaperRealization n M) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperSharpMarkerBudget n :=
  card_bankPaperMarkerRequest_le_sharpMarkerBudget n



end BankPaperRealization

/-! ## The paper-sized `O(yL)` asymptotic -/









/-! ## Sharp numerical-guard corollaries -/

namespace BankPaperRealization





theorem card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le_sharp
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (tangentEndpointGuardDeletedMultipliers u v
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
      (tangentCommonMultiplierInterval n K h u v)).card ≤
        4 + 4 * bankPaperSharpMarkerBudget n := by
  have hguard :=
    R.card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le
      (W := W) (K := K) (h := h) (u := u) (v := v)
        certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
          hyCutoff huPrime hvPrime
  have hsharp := R.prechargeComponentCount_le_sharpMarkerBudget
  omega

/-- The deterministic common-list ledger with the paper-sized sharp bank
budget substituted.  The head-residue and exceptional-row cardinalities
remain the only analytic list estimates. -/
theorem tangentPaperCommonMultiplier_sharp_finite_deletion_ledger
    {c : ℝ} {depth n M W K h Phead X0 u v : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (tangentCommonMultiplierInterval n K h u v).card ≤
      (tangentCleanCommonMultiplierList n K h Phead X0 (yNat n) u v
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)).card +
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentExceptionalMultipliers n X0 (yNat n)
        (tangentCommonMultiplierInterval n K h u v)).card +
      4 + 4 * bankPaperSharpMarkerBudget n := by
  let interval := tangentCommonMultiplierInterval n K h u v
  let numericalGuards :=
    R.tangentPaperNumericalGuardSet certificate fixedExceptional
  let dedicatedRows := R.tangentPaperDedicatedRows
  let bad := tangentCommonMultiplierBadSet
    n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards
  let clean := tangentCleanCommonMultiplierList
    n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards
  have hpartition : clean.card + bad.card = interval.card := by
    dsimp only [clean, bad, interval]
    rw [tangentCleanCommonMultiplierList_eq_sdiff_badSet]
    exact Finset.card_sdiff_add_card_eq_card
      (tangentCommonMultiplierBadSet_subset_interval
        n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards)
  have hbad := card_tangentCommonMultiplierBadSet_le
    n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards
  have hdedicated :
      (tangentDedicatedRowMultipliers (yNat n) dedicatedRows
        interval).card = 0 := by
    dsimp only [dedicatedRows, interval]
    simp
  have hguard :=
    R.card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le_sharp
      (W := W) (K := K) (h := h) (u := u) (v := v)
        certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
          hyCutoff huPrime hvPrime
  dsimp only [interval, numericalGuards, dedicatedRows, bad, clean] at hpartition hbad hdedicated hguard ⊢
  omega

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridge -/
section


/-!
# Literal canonical residual for the selector-to-tangent handoff

The canonical Saias reduction currently stops at a selector continuation: it
does not yet construct the pre-tangent rounded selector.  This file removes
the *generic residual* ambiguity without asserting that missing construction.

For a supplied selector `x`, the residual coordinate at a medium prime is
defined literally as

`valuation(selectorTailTarget) - valuation(x)`.

The two remaining selector inputs are named explicitly.  The post-rounding
prime-band balance says that these coordinates sum to zero, while prime-band
support says that the selector already has the target valuation at every
prime outside the band.  Neither fact follows merely from
`roughCanonicalRawRowQuotaError`: that quantity is a complete-rough row quota
error, not a prime-coordinate valuation identity.

From those inputs, the finite prime residual has zero total mass and its
positive star split requests have exactly the valuation deficit required by
`tangentUpdate_valuation_eq_target`.  The final theorem also retains the
all-row integrality input verbatim.  It does not claim that clean common
multipliers, feasibility of the tangent update, or the selector itself have
already been constructed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal selector deficit and its finite prime domain -/















/-! ## Prime-label geometry and exact residual algebra -/



/-- Every canonical tangent label is prime. -/
theorem bankPaperCanonicalTangentPrimeLabel_prime
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p).Prime := by
  exact prime_of_mem_primeBand p.2











/-! ## Instantiation of the star split-request boundary -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentDistributedFlowCensus -/
section


/-!
# Distributed finite-band flow census

This file isolates the quantitative interface needed between a genuine
finite-band earthmover and the already formalized split-request collision
terminal.  Unlike the one-pivot star, a distributed earthmover records a
separate port load at every vertex.  Its two analytic ledgers are

* `traffic <= (1/2) * ||residual||_1 + 2 * cutTraffic`;
* `incident(label v) <= |residual v| + 2 * portLoad v`.

These are the literal estimates produced by the cell-boundary construction
in the paper.  They are strictly stronger than the final collision target
and do not mention a density or the constant `1 / 24`.

The module proves all consequences after those construction ledgers:

* positive support has at most `|V|^2` edges;
* the total split-request count and every endpoint-label request load have
  explicit upper bounds;
* fixed main/error/ceiling parameter budgets imply the exact existing guard
  `4*T + I_source + I_target <= density^2/24` for every request;
* hence the already proved `1/8` collision-census conclusion follows.

Existence of the cell earthmover is deliberately not postulated here.  It
must be constructed from band balance, prefix-load bounds, cell cardinality,
and adjacent-cell ratio geometry.  The downstream theorems keep every
construction estimate as a visible
hypothesis, so the unfinished construction cannot be confused with a
selector theorem or with the final collision target.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Residual, cut, and port ledgers -/









/-! ## Literal ratio-cell cuts and uniform adjacent-cell ports -/

























/-- A positive edge of a cell-respecting flow joins equal or adjacent ratio
cells. -/
theorem tangentPositiveEdge_sameOrAdjacentRatioCell
    {V Band : Type*} [Fintype V] [DecidableEq V]
    {bandOf : V -> Band} {cellIndex : V -> Nat} {flow : V -> V -> Real}
    (hrespect : TangentFlowRespectsRatioCells bandOf cellIndex flow)
    {edge : V × V} (hedge : edge ∈ tangentPositiveFlowEdges flow) :
    TangentSameOrAdjacentRatioCell bandOf cellIndex edge.1 edge.2 := by
  exact hrespect (mem_tangentPositiveFlowEdges.mp hedge)

/-- Ratio-cell geometry converts positive-edge adjacency into the required
endpoint-ratio bound. -/
theorem tangentPositiveEdge_locality_of_ratioCells
    {V Band : Type*} [Fintype V] [DecidableEq V]
    (label : V -> Nat) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (flow : V -> V -> Real) (ratioUpper : Real)
    (hrespect : TangentFlowRespectsRatioCells bandOf cellIndex flow)
    (hgeometry : TangentRatioCellGeometry
      label bandOf cellIndex ratioUpper)
    {edge : V × V} (hedge : edge ∈ tangentPositiveFlowEdges flow) :
    (((max (tangentStarEdgeSource label edge)
          (tangentStarEdgeTarget label edge) : Nat) : Real) /
        ((min (tangentStarEdgeSource label edge)
          (tangentStarEdgeTarget label edge) : Nat) : Real)) <= ratioUpper := by
  exact hgeometry
    (tangentPositiveEdge_sameOrAdjacentRatioCell hrespect hedge)















/-! ## Visible hypotheses for a distributed construction -/

/- The construction estimates are deliberately *not* bundled into a
structure.  The repository audit discipline forbids hiding a claimed
traffic or incident estimate in a conclusion-bearing certificate.  Every
generic theorem below therefore displays the exact flow property that it
uses. -/

/-! ## Support, locality, and literal traffic consequences -/









/-! ## Boundary preservation for an arbitrary distributed flow -/









/-! ## Weighted per-label port control -/









/-! ## Total and endpoint request counts -/









/-! ## Paper-parameter closure of the collision guard

The three budgets below mirror the actual parameter order in Section 9.
The main term is made small by the fixed band width `w`; the error and
ceiling terms are absorbed only after the mesh is fixed and `n` tends to
infinity.  None of them is a traffic or request-count hypothesis. -/















/-! ## Connector to the actual paper collision terminal -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentBalancedProductFlow -/
section


/-!
# Canonical balanced product transport

For a finite signed residual of total mass zero, this file gives the
explicit dense transport

`max (q u) 0 * max (-q v) 0 / sum_w max (q w) 0`.

Thus every positive coordinate sends its mass proportionally to all
negative coordinates.  The construction is nonnegative, has no loops,
has divergence exactly `q`, total traffic exactly half the `ell^1` mass,
and incident traffic at `v` exactly `|q v|`.  The last identity is why this
construction is used inside a ratio cell: a star or a deterministic chain
would concentrate the internal traffic at a pivot and would not give the
paper's pointwise endpoint ledger.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem tangentPositiveMass_nonneg
    {V : Type*} [Fintype V] (q : V -> Real) :
    0 <= tangentPositiveMass q := by
  unfold tangentPositiveMass
  exact Finset.sum_nonneg fun v _hv => le_max_right (q v) 0







theorem tangentBalancedProductFlow_nonneg
    {V : Type*} [Fintype V] (q : V -> Real)
    (source target : V) :
    0 <= tangentBalancedProductFlow q source target := by
  unfold tangentBalancedProductFlow
  exact div_nonneg
    (mul_nonneg (le_max_right (q source) 0)
      (le_max_right (-q target) 0))
    (tangentPositiveMass_nonneg q)





















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentRatioCellEarthmover -/
section


/-!
# Explicit ratio-cell earthmover

This file implements the missing finite transport layer behind
`TangentDistributedFlowCensus`.

Inside every exponent band the occupied ratio cells are numbered
`0, ..., lastCell b`.  At the cut after cell `i` the signed prefix mass
`F_i` is spread uniformly over the complete bipartite graph joining cells
`i` and `i+1`, in the direction determined by the sign of `F_i`.  After
these boundary transports, the adjusted residual `q_p` has sum zero in
each cell.  It is transported by the canonical proportional matching from
`TangentBalancedProductFlow`.

The resulting flow is a visible formula, not a conclusion-bearing
certificate.  Its divergence, locality, traffic, and pointwise incident
estimates are theorems.  In particular, no final collision smallness bound
is assumed or stored here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Uniform cell weights and one boundary cut -/









theorem tangentRatioCellUniformWeight_nonneg
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cell : Nat) (v : V) :
    0 <= tangentRatioCellUniformWeight bandOf cellIndex band cell v := by
  unfold tangentRatioCellUniformWeight
  split_ifs <;> positivity







theorem tangentRatioCellBoundaryCutFlow_nonneg
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (source target : V) :
    0 <= tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target := by
  unfold tangentRatioCellBoundaryCutFlow
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (le_max_right _ _)
        (tangentRatioCellUniformWeight_nonneg
          bandOf cellIndex band cut source))
      (tangentRatioCellUniformWeight_nonneg
        bandOf cellIndex band (cut + 1) target))
    (mul_nonneg
      (mul_nonneg (le_max_right _ _)
        (tangentRatioCellUniformWeight_nonneg
          bandOf cellIndex band (cut + 1) source))
      (tangentRatioCellUniformWeight_nonneg
        bandOf cellIndex band cut target))





















/-! ## Finite-sum linearity for flows -/







/-! ## All canonical cuts in one finite band family -/





theorem tangentRatioCellBoundaryFlow_nonneg
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) :
    0 <= tangentRatioCellBoundaryFlow
      lastCell residual bandOf cellIndex source target := by
  unfold tangentRatioCellBoundaryFlow
  exact Finset.sum_nonneg fun band _hband =>
    Finset.sum_nonneg fun cut _hcut =>
      tangentRatioCellBoundaryCutFlow_nonneg
        residual bandOf cellIndex band cut source target



/-! ## Prefix algebra and exact boundary divergence -/























/-! ## The balanced residual inside each cell -/





theorem tangentRatioCellInternalFlow_nonneg
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) :
    0 <= tangentRatioCellInternalFlow
      lastCell residual bandOf cellIndex source target := by
  unfold tangentRatioCellInternalFlow
  exact Finset.sum_nonneg fun band _hband =>
    Finset.sum_nonneg fun cell _hcell =>
      tangentBalancedProductFlow_nonneg
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target

























/-! ## Support locality -/

theorem tangentRatioCellBoundaryCutFlow_positive_cells
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    {source target : V}
    (hflow : 0 < tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target) :
    ((bandOf source = band ∧ cellIndex source = cut) ∧
        (bandOf target = band ∧ cellIndex target = cut + 1)) ∨
      ((bandOf source = band ∧ cellIndex source = cut + 1) ∧
        (bandOf target = band ∧ cellIndex target = cut)) := by
  by_cases hsourceLeft : bandOf source = band ∧ cellIndex source = cut
  · by_cases htargetRight :
        bandOf target = band ∧ cellIndex target = cut + 1
    · exact Or.inl ⟨hsourceLeft, htargetRight⟩
    · have hsourceRight :
          ¬(bandOf source = band ∧ cellIndex source = cut + 1) := by
        intro h
        omega
      simp [tangentRatioCellBoundaryCutFlow,
        tangentRatioCellUniformWeight, htargetRight, hsourceRight] at hflow
  · by_cases hsourceRight :
        bandOf source = band ∧ cellIndex source = cut + 1
    · by_cases htargetLeft :
          bandOf target = band ∧ cellIndex target = cut
      · exact Or.inr ⟨hsourceRight, htargetLeft⟩
      · simp [tangentRatioCellBoundaryCutFlow,
          tangentRatioCellUniformWeight, hsourceLeft, htargetLeft] at hflow
    · simp [tangentRatioCellBoundaryCutFlow,
        tangentRatioCellUniformWeight, hsourceLeft, hsourceRight] at hflow

theorem tangentRatioCellBoundaryCutFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    {source target : V}
    (hflow : 0 < tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target) :
    TangentSameOrAdjacentRatioCell bandOf cellIndex source target := by
  rcases tangentRatioCellBoundaryCutFlow_positive_cells
      residual bandOf cellIndex band cut hflow with hforward | hbackward
  · rcases hforward with ⟨⟨hsband, hscell⟩, ⟨htband, htcell⟩⟩
    exact ⟨hsband.trans htband.symm, Or.inr (Or.inl (by omega))⟩
  · rcases hbackward with ⟨⟨hsband, hscell⟩, ⟨htband, htcell⟩⟩
    exact ⟨hsband.trans htband.symm, Or.inr (Or.inr (by omega))⟩

theorem tangentRatioCellBoundaryFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) :
    TangentFlowRespectsRatioCells bandOf cellIndex
      (tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex) := by
  intro source target hflow
  unfold tangentRatioCellBoundaryFlow at hflow
  have houterNonneg : forall band : Band,
      0 <= ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellBoundaryCutFlow
          residual bandOf cellIndex band cut source target := by
    intro band
    exact Finset.sum_nonneg fun cut _hcut =>
      tangentRatioCellBoundaryCutFlow_nonneg
        residual bandOf cellIndex band cut source target
  obtain ⟨band, _hband, hbandPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun band _hband => houterNonneg band)).mp hflow
  obtain ⟨cut, hcut, hcutPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun cut _hcut => tangentRatioCellBoundaryCutFlow_nonneg
        residual bandOf cellIndex band cut source target)).mp hbandPos
  exact tangentRatioCellBoundaryCutFlow_respectsRatioCells
    residual bandOf cellIndex band cut hcutPos

theorem tangentBalancedProductFlow_masked_positive_cells
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cell : Nat)
    {source target : V}
    (hflow : 0 < tangentBalancedProductFlow
      (tangentRatioCellMaskedInternalResidual
        residual bandOf cellIndex band cell) source target) :
    (bandOf source = band ∧ cellIndex source = cell) ∧
      (bandOf target = band ∧ cellIndex target = cell) := by
  by_cases hsource : bandOf source = band ∧ cellIndex source = cell
  · by_cases htarget : bandOf target = band ∧ cellIndex target = cell
    · exact ⟨hsource, htarget⟩
    · simp [tangentBalancedProductFlow,
        tangentRatioCellMaskedInternalResidual, htarget] at hflow
  · simp [tangentBalancedProductFlow,
      tangentRatioCellMaskedInternalResidual, hsource] at hflow

theorem tangentRatioCellInternalFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) :
    TangentFlowRespectsRatioCells bandOf cellIndex
      (tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex) := by
  intro source target hflow
  unfold tangentRatioCellInternalFlow at hflow
  have houterNonneg : forall band : Band,
      0 <= ∑ cell ∈ Finset.range (lastCell band + 1),
        tangentBalancedProductFlow
          (tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell) source target := by
    intro band
    exact Finset.sum_nonneg fun cell _hcell =>
      tangentBalancedProductFlow_nonneg
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target
  obtain ⟨band, _hband, hbandPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun band _hband => houterNonneg band)).mp hflow
  obtain ⟨cell, hcell, hcellPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun cell _hcell => tangentBalancedProductFlow_nonneg
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target)).mp hbandPos
  rcases tangentBalancedProductFlow_masked_positive_cells
      residual bandOf cellIndex band cell hcellPos with
    ⟨⟨hsband, hscell⟩, ⟨htband, htcell⟩⟩
  exact ⟨hsband.trans htband.symm, Or.inl (hscell.trans htcell.symm)⟩

/-! ## The complete explicit earthmover -/















theorem tangentRatioCellEarthmoverFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) :
    TangentFlowRespectsRatioCells bandOf cellIndex
      (tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex) := by
  intro source target hflow
  have hboundaryNonneg := tangentRatioCellBoundaryFlow_nonneg
    lastCell residual bandOf cellIndex source target
  have hinternalNonneg := tangentRatioCellInternalFlow_nonneg
    lastCell residual bandOf cellIndex source target
  unfold tangentRatioCellEarthmoverFlow at hflow
  by_cases hboundary :
      0 < tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex source target
  · exact tangentRatioCellBoundaryFlow_respectsRatioCells
      lastCell residual bandOf cellIndex hboundary
  · have hinternal :
        0 < tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex source target := by
      have hboundaryZero :
          tangentRatioCellBoundaryFlow
            lastCell residual bandOf cellIndex source target = 0 :=
        le_antisymm (le_of_not_gt hboundary) hboundaryNonneg
      linarith
    exact tangentRatioCellInternalFlow_respectsRatioCells
      lastCell residual bandOf cellIndex hinternal

















/-! ## From full vertex incident mass to the positive-support census -/











/-- Fixed-ratio geometry turns the proved cell support into the literal
edge-locality inequality. -/
theorem tangentRatioCellEarthmoverFlow_positiveEdge_locality
    {V Band : Type*} [Fintype V] [DecidableEq V]
    [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (label : V -> Nat) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (ratioUpper : Real)
    (hgeometry : TangentRatioCellGeometry
      label bandOf cellIndex ratioUpper)
    {edge : V × V}
    (hedge : edge ∈ tangentPositiveFlowEdges
      (tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex)) :
    (((max (label edge.1) (label edge.2) : Nat) : Real) /
      ((min (label edge.1) (label edge.2) : Nat) : Real)) <= ratioUpper := by
  simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using
    tangentPositiveEdge_locality_of_ratioCells
      label bandOf cellIndex
      (tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex) ratioUpper
      (tangentRatioCellEarthmoverFlow_respectsRatioCells
        lastCell residual bandOf cellIndex) hgeometry hedge





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentExceptionalSelbergReduction -/
section


/-!
# Exceptional tangent rows: the verified Selberg reduction

Section 9 of the paper bounds the common multipliers with
`2n / R_y(a) < X0` by writing

`a = R_y(a) * b`

and applying an interval Selberg sieve separately for each smooth factor
`b`.  This file formalizes all of that finite reduction and connects it to
the literal common-list deletion ledger.

The analytic availability boundary is important here.  The Mathlib module
`Mathlib.NumberTheory.SelbergSieve` currently supplies the abstract theorem

`BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`,

but it does not yet construct the paper's Lambda-squared coefficients,
diagonalize their main term, or prove the required lower bound for the
sieve-density sum.  In particular, the specialized estimate

`H / log y + y^4 / (log y)^2`

cannot honestly be deduced from the available library theorem alone.
Accordingly, this file does not assume that estimate or its desired
cardinality consequence.  It proves instead the strongest available
statement:

* the interval sieve is a literal `BoundingSieve` with `nu(d)=1/d`;
* its remainder has the sharp elementary bound `|R_d| < 1`;
* every exceptional common multiplier injects into the disjoint union of
  the corresponding rough reduced-residue intervals;
* any verified upper-Moebius coefficients therefore give an explicit real
  majorant, and its natural ceiling substitutes for the exceptional term in
  both the generic and the sharp bank deletion ledgers.

Thus, at this reduction layer, the analytic obligation is isolated exactly
as the choice and estimation of concrete upper-Moebius coefficients, rather
than hidden inside an assumed exceptional-cardinality bound.  The downstream
Lambda-square modules discharge that obligation.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## A literal interval `BoundingSieve` -/







/-- The product of the distinct primes at most `y` is squarefree. -/
theorem roughHeadModulus_squarefree (y : ℕ) :
    Squarefree (roughHeadModulus y) := by
  unfold roughHeadModulus
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes
        (mem_primesUpTo.mp hp).1 (mem_primesUpTo.mp hq).1).mpr hpq)
  · intro p hp
    exact (mem_primesUpTo.mp hp).1.squarefree

/-- Every prime in a complete rough label is absent from the head-prime
product at the same cutoff. -/
theorem completeRoughLabel_coprime_roughHeadModulus (y a : ℕ) :
    Nat.Coprime (completeRoughLabel y a) (roughHeadModulus y) := by
  apply Nat.coprime_of_dvd
  intro p hp hpLabel hpHead
  have hpHigh : y < p :=
    prime_dvd_completeRoughLabel_gt hp hpLabel
  rw [roughHeadModulus] at hpHead
  obtain ⟨q, hqHead, hpq⟩ :=
    (hp.prime.dvd_finset_prod_iff id).mp hpHead
  have hq := mem_primesUpTo.mp hqHead
  have hpEq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hq.1).mp hpq
  omega



/-- The sifted sum of the literal interval sieve is exactly the cardinality
of its reduced-residue interval. -/
theorem tangentIntervalReciprocalSieve_siftedSum
    (P lo hi : ℕ) (hP : Squarefree P) :
    (tangentIntervalReciprocalSieve P lo hi hP).siftedSum =
      ((reducedResidueIoc P lo hi).card : ℝ) := by
  simp [tangentIntervalReciprocalSieve, BoundingSieve.siftedSum,
    reducedResidueIoc, Nat.coprime_comm]

/-- Direct specialization of Mathlib's strongest currently available
Selberg theorem to a literal reduced-residue interval. -/
theorem reducedResidueIoc_card_le_abstractSelberg
    {P lo hi : ℕ} (hP : Squarefree P)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      let s := tangentIntervalReciprocalSieve P lo hi hP
      s.totalMass * s.mainSum muPlus + s.errSum muPlus := by
  let s := tangentIntervalReciprocalSieve P lo hi hP
  have hs := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    muPlus hmuPlus
  simpa only [s, tangentIntervalReciprocalSieve_siftedSum] using hs

/-! ## The exact endpoint remainder, with constant one -/

/-- The number of multiples of `D` in `(lo,hi]` is the difference of the
two endpoint quotients. -/
theorem Ioc_filter_dvd_card_eq_div_sub_div
    {D lo hi : ℕ} (hD : 0 < D) :
    ((Finset.Ioc lo hi).filter (D ∣ ·)).card = hi / D - lo / D := by
  simpa [coprimeMultipleIoc, reducedResidueIoc] using
    (coprimeMultipleIoc_card_eq_reducedResidueIoc
      (M := 1) (D := D) (lo := lo) (hi := hi) hD
      (by simp : Nat.Coprime D 1))

/-- Exact multiple count inside the interval sieve. -/
theorem tangentIntervalReciprocalSieve_multSum
    {P lo hi D : ℕ} (hP : Squarefree P) (hD : 0 < D) :
    (tangentIntervalReciprocalSieve P lo hi hP).multSum D =
      ((hi / D - lo / D : ℕ) : ℝ) := by
  rw [BoundingSieve.multSum]
  simp only [tangentIntervalReciprocalSieve, Finset.sum_boole]
  exact_mod_cast Ioc_filter_dvd_card_eq_div_sub_div hD

/-- The elementary interval remainder costs strictly less than one for
every positive divisor.  This is the precise constant entering the
non-diagonalized abstract Selberg error sum. -/
theorem tangentIntervalReciprocalSieve_rem_abs_lt_one
    {P lo hi D : ℕ} (hP : Squarefree P) (hD : 0 < D)
    (hlohi : lo ≤ hi) :
    |(tangentIntervalReciprocalSieve P lo hi hP).rem D| < 1 := by
  rw [BoundingSieve.rem,
    tangentIntervalReciprocalSieve_multSum hP hD]
  simp only [tangentIntervalReciprocalSieve,
    tangentReciprocalArithmeticFunction_apply_of_pos hD]
  simpa [div_eq_mul_inv, mul_comm] using
    (quotientIocLength_sub_realLengthDiv_abs_lt_one hD hlohi)

/-- Total form of the remainder bound.  If the endpoints are reversed,
both the support and its declared natural length are zero, so the remainder
vanishes. -/
theorem tangentIntervalReciprocalSieve_rem_abs_lt_one_total
    {P lo hi D : ℕ} (hP : Squarefree P) (hD : 0 < D) :
    |(tangentIntervalReciprocalSieve P lo hi hP).rem D| < 1 := by
  by_cases hlohi : lo ≤ hi
  · exact tangentIntervalReciprocalSieve_rem_abs_lt_one hP hD hlohi
  · have hhilo : hi ≤ lo := (Nat.lt_of_not_ge hlohi).le
    have hsupport : Finset.Ioc lo hi = ∅ :=
      Finset.Ioc_eq_empty_of_le hhilo
    rw [BoundingSieve.rem]
    simp [tangentIntervalReciprocalSieve, hsupport,
      Nat.sub_eq_zero_of_le hhilo]

/-- Consequently the abstract error sum is bounded by the exact `l1` norm
of the chosen upper-Moebius coefficients over divisors of `P`. -/
theorem tangentIntervalReciprocalSieve_errSum_le_l1
    {P lo hi : ℕ} (hP : Squarefree P) (muPlus : ℕ → ℝ) :
    (tangentIntervalReciprocalSieve P lo hi hP).errSum muPlus ≤
      ∑ D ∈ P.divisors, |muPlus D| := by
  rw [BoundingSieve.errSum]
  apply Finset.sum_le_sum
  intro D hD
  have hDPos : 0 < D := Nat.pos_of_mem_divisors hD
  calc
    |muPlus D| *
        |(tangentIntervalReciprocalSieve P lo hi hP).rem D| ≤
        |muPlus D| * 1 :=
      mul_le_mul_of_nonneg_left
        (tangentIntervalReciprocalSieve_rem_abs_lt_one_total
          hP hDPos).le (abs_nonneg _)
    _ = |muPlus D| := mul_one _

/-- Fully explicit form of the currently verified interval Selberg
reduction: the main sum is left visible, while every interval remainder has
already been replaced by its sharp constant-one bound. -/
theorem reducedResidueIoc_card_le_abstractSelberg_l1
    {P lo hi : ℕ} (hP : Squarefree P) (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) *
          (tangentIntervalReciprocalSieve P lo hi hP).mainSum muPlus +
        ∑ D ∈ P.divisors, |muPlus D| := by
  calc
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
        let s := tangentIntervalReciprocalSieve P lo hi hP
        s.totalMass * s.mainSum muPlus + s.errSum muPlus :=
      reducedResidueIoc_card_le_abstractSelberg hP muPlus hmuPlus
    _ ≤ ((hi - lo : ℕ) : ℝ) *
          (tangentIntervalReciprocalSieve P lo hi hP).mainSum muPlus +
        ∑ D ∈ P.divisors, |muPlus D| := by
      simpa only [tangentIntervalReciprocalSieve] using
        add_le_add_right
          (tangentIntervalReciprocalSieve_errSum_le_l1 hP muPlus)
          (((hi - lo : ℕ) : ℝ) *
            (tangentIntervalReciprocalSieve P lo hi hP).mainSum muPlus)

/-! ## Exact factorization of exceptional common multipliers -/



/-- The exact `u*b<X0` index set has at most `X0/u` elements.  This is the
finite source of the paper's factor `X0/u` in the accumulated `y^4`
remainder. -/
theorem card_tangentExceptionalSmoothIndices_le_div
    {X0 u : ℕ} (hu : 0 < u) :
    (tangentExceptionalSmoothIndices X0 u).card ≤ X0 / u := by
  calc
    (tangentExceptionalSmoothIndices X0 u).card ≤
        (Finset.Icc 1 (X0 / u)).card := by
      apply Finset.card_le_card
      intro b hb
      have hbData := Finset.mem_filter.mp hb
      apply Finset.mem_Icc.mpr
      refine ⟨(Finset.mem_Icc.mp hbData.1).1, ?_⟩
      apply (Nat.le_div_iff_mul_le hu).mpr
      simpa only [Nat.mul_comm] using hbData.2.le
    _ ≤ X0 / u := by simp













/-- Exact product recovery makes the rough/smooth coordinate map globally
injective, not merely injective on the exceptional set. -/
theorem tangentRoughDecompositionIndex_injective (y : ℕ) :
    Function.Injective (tangentRoughDecompositionIndex y) := by
  intro a₁ a₂ hindex
  have hproduct := congrArg
    (fun z : Σ _b : ℕ, ℕ ↦ z.2 * z.1) hindex
  simpa only [tangentRoughDecompositionIndex,
    completeRoughLabel_mul_completeSmoothPart] using hproduct

/-- Every exceptional multiplier in `I_uv` lands in its claimed fixed-`b`
reduced-residue interval.  The exact finite relations are

`u*b < X0`, `n/(vb) < R`, and `R ≤ (2n-Kh)/(ub)`.

The first is a sharpened consequence of the physical upper endpoint and in
particular implies the paper's deliberately looser bound `b < 2*X0/u`.
-/
theorem tangentRoughDecompositionIndex_mem_exceptionalSievePairs
    {n K h X0 y u v a : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (ha : a ∈ tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)) :
    tangentRoughDecompositionIndex y a ∈
      tangentExceptionalSievePairs n K h X0 y u v := by
  rw [tangentExceptionalMultipliers, Finset.mem_filter] at ha
  have haBounds := mem_tangentCommonMultiplierInterval.mp ha.1
  have haPos : 0 < a := by
    have hzero : 0 ≤ n / v := Nat.zero_le _
    omega
  let R := completeRoughLabel y a
  let b := completeSmoothPart y a
  have hRPos : 0 < R := by
    exact completeRoughLabel_pos y a
  have hbPos : 0 < b := by
    exact completeSmoothPart_pos haPos
  have hdecomp : R * b = a := by
    exact completeRoughLabel_mul_completeSmoothPart y a
  have hTwoN : 2 * n < X0 * R := by
    exact (Nat.div_lt_iff_lt_mul hRPos).mp ha.2
  have huaUpper : u * a ≤ tangentBroadUpper n K h := by
    have h := (Nat.le_div_iff_mul_le hu).mp haBounds.2
    simpa only [Nat.mul_comm] using h
  have hubLt : u * b < X0 := by
    apply (Nat.mul_lt_mul_left hRPos).mp
    calc
      R * (u * b) = u * a := by rw [← hdecomp]; ac_rfl
      _ ≤ tangentBroadUpper n K h := huaUpper
      _ ≤ 2 * n := Nat.sub_le _ _
      _ < X0 * R := hTwoN
      _ = R * X0 := Nat.mul_comm _ _
  have hbLeX0 : b ≤ X0 := by
    exact (Nat.le_mul_of_pos_left b hu).trans hubLt.le
  have hnLower : n / (v * b) < R := by
    apply (Nat.div_lt_iff_lt_mul (mul_pos hv hbPos)).mpr
    have hnva : n < v * a := by
      have h := (Nat.div_lt_iff_lt_mul hv).mp haBounds.1
      simpa only [Nat.mul_comm] using h
    calc
      n < v * a := hnva
      _ = R * (v * b) := by rw [← hdecomp]; ac_rfl
  have hRUpper : R ≤ tangentBroadUpper n K h / (u * b) := by
    apply (Nat.le_div_iff_mul_le (mul_pos hu hbPos)).mpr
    calc
      R * (u * b) = u * a := by rw [← hdecomp]; ac_rfl
      _ ≤ tangentBroadUpper n K h := huaUpper
  rw [tangentExceptionalSievePairs, Finset.mem_sigma]
  dsimp only [tangentRoughDecompositionIndex]
  constructor
  · rw [tangentExceptionalSmoothIndices, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨hbPos, hbLeX0⟩, hubLt⟩
  · rw [tangentExceptionalRoughCandidates, reducedResidueIoc,
      Finset.mem_filter]
    exact ⟨Finset.mem_Ioc.mpr ⟨hnLower, hRUpper⟩,
      completeRoughLabel_coprime_roughHeadModulus y a⟩

/-- Maximal unconditional finite reduction of the exceptional count to the
sum of the fixed-smooth-factor rough interval counts. -/
theorem card_tangentExceptionalMultipliers_le_sieveSum
    {n K h X0 y u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    (tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v)).card ≤
      ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (tangentExceptionalRoughCandidates n K h y u v b).card := by
  classical
  let exceptional := tangentExceptionalMultipliers n X0 y
    (tangentCommonMultiplierInterval n K h u v)
  let pairs := tangentExceptionalSievePairs n K h X0 y u v
  let decompose := tangentRoughDecompositionIndex y
  calc
    exceptional.card = (exceptional.image decompose).card :=
      (Finset.card_image_of_injective exceptional
        (tangentRoughDecompositionIndex_injective y)).symm
    _ ≤ pairs.card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨a, haExceptional, rfl⟩ := Finset.mem_image.mp hz
      exact tangentRoughDecompositionIndex_mem_exceptionalSievePairs
        hu hv haExceptional
    _ = ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (tangentExceptionalRoughCandidates n K h y u v b).card := by
      simp only [pairs, tangentExceptionalSievePairs, Finset.card_sigma]

/-! ## Substitution of the verified abstract sieve bound -/

















/-! ## The `delta_* < 1/18`, `y^4=n^(8/9)` remainder arithmetic -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCleanListCardinalityBridge -/
section


/-!
# Cardinality bridge for the tangent clean common list

This file performs the final finite-cardinality assembly around the tangent
common list.  The head-coprime candidates are the literal reduced residues in
the common-multiplier interval.  Their complement is exactly the already
defined head-bad set, so the head-bad term cancels from the finite-deletion
ledger.

The resulting theorems turn a supplied lower bound for those interval
candidates, supplied upper bounds for the exceptional and remaining deletion
losses, and one explicit natural-number comparison into

`lowerCard ≤ cleanList.card`.

This is the bridge which discharges the `hlower` input of the later
collision-counting terminal when supplied the paper's analytic estimates.
It does not prove any reduced-residue density estimate, exceptional-row
estimate, or final numerical comparison.  Those inputs remain visible in the
statements below.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal head-coprime interval candidates -/



/-- The head-coprime candidates are literally the fixed-modulus
reduced-residue count on `(n / v, (2n-Kh) / u]`. -/
theorem tangentHeadCoprimeCandidates_eq_reducedResidueIoc
    (n K h Phead u v : ℕ) :
    tangentHeadCoprimeCandidates n K h Phead u v =
      reducedResidueIoc Phead (n / v) (tangentBroadUpper n K h / u) := by
  rfl

/-- The head-coprime candidates and the head-bad multipliers partition the
literal common interval. -/
theorem card_tangentHeadCoprimeCandidates_add_headBad
    (n K h Phead u v : ℕ) :
    (tangentHeadCoprimeCandidates n K h Phead u v).card +
        (tangentHeadBadMultipliers Phead
          (tangentCommonMultiplierInterval n K h u v)).card =
      (tangentCommonMultiplierInterval n K h u v).card := by
  simpa only [tangentHeadCoprimeCandidates,
    tangentHeadBadMultipliers] using
    (Finset.card_filter_add_card_filter_not
      (s := tangentCommonMultiplierInterval n K h u v)
      (fun a : ℕ ↦ Nat.Coprime a Phead))

/-! ## Generic finite-deletion assembly -/



/-! ## Actual-paper sharp specializations -/

/-- Paper-bank specialization of the cardinality bridge.  The dedicated-row
loss has already vanished in the sharp ledger and the numerical-guard loss is
the audited `4 + 4 * bankPaperSharpMarkerBudget n`.  Among deletion counts,
only an explicit exceptional upper bound remains; the candidate lower bound
and the final natural-number comparison are also explicit premises. -/
theorem BankPaperRealization.tangentPaperCleanCommonMultiplierList_card_lower_of_headCandidate
    {c : ℝ} {depth n M W K h Phead X0 u v : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime)
    {candidateLower exceptionalUpper lowerCard : ℕ}
    (hcandidate :
      candidateLower ≤
        (tangentHeadCoprimeCandidates n K h Phead u v).card)
    (hexceptional :
      (tangentExceptionalMultipliers n X0 (yNat n)
        (tangentCommonMultiplierInterval n K h u v)).card ≤
          exceptionalUpper)
    (harithmetic :
      lowerCard + exceptionalUpper + 4 +
          4 * bankPaperSharpMarkerBudget n ≤ candidateLower) :
    lowerCard ≤
      (tangentCleanCommonMultiplierList n K h Phead X0 (yNat n) u v
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet
          certificate fixedExceptional)).card := by
  have hledger :=
    R.tangentPaperCommonMultiplier_sharp_finite_deletion_ledger
      (W := W) (K := K) (h := h) (Phead := Phead) (X0 := X0)
        (u := u) (v := v) certificate fixedExceptional hfixedTail hTwoW
          hPrefix hWv hvu huy hyCutoff huPrime hvPrime
  have hpartition := card_tangentHeadCoprimeCandidates_add_headBad
    n K h Phead u v
  omega



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentExceptionalLambdaSquareSieve -/
section


/-!
# Concrete finite Lambda-squared coefficients for the exceptional-row sieve

This file continues the Section 9 Selberg reduction past the abstract
`IsUpperMoebius` interface.  For a finite divisor support

`S(P,R) = {d : d | P, d <= R}`

and real weights `lambda_d`, it defines the literal Lambda-squared
coefficients

`muPlus(q) = sum_{d,e in S(P,R), lcm(d,e)=q} lambda_d lambda_e`.

The divisor sum of these coefficients is proved to be the square

`sum_{q|m} muPlus(q) = (sum_{d in S(P,R), d|m} lambda_d)^2`.

Consequently `lambda_1=1` gives a genuine upper-Moebius sequence.  We also
prove the exact quadratic main-term identity, the level-squared support
bound, and the sharp finite `l1` estimate obtained by partitioning pairs by
their least common multiple.  These yield a concrete interval upper sieve;
no exceptional-cardinality conclusion is assumed.

Finally, the file defines the canonical finite Selberg weights by Mobius
inversion of the diagonal target.  Their normalization `lambda_1=1`, exact
diagonal transform, and optimal quadratic value `1/G(P,R)` are proved here.
The downstream canonical-bounds layer lower-bounds the finite density sum
and upper-bounds the canonical coefficient norm.
-/

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

noncomputable section

/-! ## Finite Lambda-squared coefficients -/





theorem tangentSelbergLambdaSupport_pos
    {P R d : ℕ} (hd : d ∈ tangentSelbergLambdaSupport P R) :
    0 < d := by
  exact Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1

theorem one_mem_tangentSelbergLambdaSupport
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    1 ∈ tangentSelbergLambdaSupport P R := by
  simp [tangentSelbergLambdaSupport, hP.ne', hR]





/-- Exact square identity behind the Lambda-squared upper sieve. -/
theorem sum_tangentSelbergLambdaSquareCoefficient_divisors
    {P R m : ℕ} (lambda : ℕ → ℝ) (hm : 0 < m) :
    (∑ q ∈ m.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q) =
      tangentSelbergLambdaLinearForm P R lambda m ^ 2 := by
  classical
  let S := tangentSelbergLambdaSupport P R
  change
    (∑ q ∈ m.divisors,
      ∑ d ∈ S, ∑ e ∈ S,
        if Nat.lcm d e = q then lambda d * lambda e else 0) =
      (∑ d ∈ S, if d ∣ m then lambda d else 0) ^ 2
  calc
    (∑ q ∈ m.divisors,
      ∑ d ∈ S, ∑ e ∈ S,
        if Nat.lcm d e = q then lambda d * lambda e else 0) =
        ∑ d ∈ S, ∑ e ∈ S, ∑ q ∈ m.divisors,
          if Nat.lcm d e = q then lambda d * lambda e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ S, ∑ e ∈ S,
        if d ∣ m ∧ e ∣ m then lambda d * lambda e else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      simp [Nat.mem_divisors, hm.ne', Nat.lcm_dvd_iff]
    _ = (∑ d ∈ S, if d ∣ m then lambda d else 0) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hdm : d ∣ m <;> by_cases hem : e ∣ m <;>
        simp [hdm, hem]

/-- A normalized finite Lambda family gives actual upper-Moebius
coefficients, including at Mathlib's total boundary `m=0`. -/
theorem tangentSelbergLambdaSquareCoefficient_isUpperMoebius
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1) :
    BoundingSieve.IsUpperMoebius
      (tangentSelbergLambdaSquareCoefficient P R lambda) := by
  intro m
  by_cases hm0 : m = 0
  · subst m
    simp
  · rw [sum_tangentSelbergLambdaSquareCoefficient_divisors
      lambda (Nat.pos_of_ne_zero hm0)]
    by_cases hm1 : m = 1
    · subst m
      simp [tangentSelbergLambdaLinearForm,
        tangentSelbergLambdaSupport, Nat.dvd_one, hP.ne', hR,
        hlambdaOne]
    · rw [if_neg hm1]
      exact sq_nonneg _

/-! ## Level support and exact quadratic moment -/



/-- Summing the grouped coefficients against an arbitrary function simply
evaluates that function at each pair's lcm. -/
theorem tangentSelbergLambdaSquareCoefficient_divisorMoment
    {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ P.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q * F q) =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e * F (Nat.lcm d e) := by
  classical
  let S := tangentSelbergLambdaSupport P R
  change
    (∑ q ∈ P.divisors,
      (∑ d ∈ S, ∑ e ∈ S,
        if Nat.lcm d e = q then lambda d * lambda e else 0) * F q) =
      ∑ d ∈ S, ∑ e ∈ S,
        lambda d * lambda e * F (Nat.lcm d e)
  calc
    (∑ q ∈ P.divisors,
      (∑ d ∈ S, ∑ e ∈ S,
        if Nat.lcm d e = q then lambda d * lambda e else 0) * F q) =
        ∑ q ∈ P.divisors, ∑ d ∈ S, ∑ e ∈ S,
          if Nat.lcm d e = q then
            lambda d * lambda e * F q else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _he
      split_ifs <;> simp_all
    _ = ∑ d ∈ S, ∑ e ∈ S, ∑ q ∈ P.divisors,
        if Nat.lcm d e = q then
          lambda d * lambda e * F q else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ S, ∑ e ∈ S,
        lambda d * lambda e * F (Nat.lcm d e) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      have hdP : d ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      have heP : e ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
      have hlcmMem : Nat.lcm d e ∈ P.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.lcm_dvd hdP heP, hP.ne'⟩
      simp [hlcmMem]

/-- Exact quadratic main sum for the density `nu(q)=1/q`. -/
theorem tangentSelbergLambdaSquare_mainQuadraticIdentity
    {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) :
    (∑ q ∈ P.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q /
          (q : ℝ)) =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e / (Nat.lcm d e : ℝ) := by
  simpa only [div_eq_mul_inv, one_mul] using
    (tangentSelbergLambdaSquareCoefficient_divisorMoment
      hP lambda (fun q ↦ 1 / (q : ℝ)))

/-- The `mainSum` of the literal interval sieve is exactly the preceding
finite quadratic form. -/
theorem tangentIntervalReciprocalSieve_lambdaSquare_mainSum
    {P R lo hi : ℕ} (hP : Squarefree P) (lambda : ℕ → ℝ) :
    (tangentIntervalReciprocalSieve P lo hi hP).mainSum
        (tangentSelbergLambdaSquareCoefficient P R lambda) =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e / (Nat.lcm d e : ℝ) := by
  rw [BoundingSieve.mainSum]
  calc
    (∑ q ∈ P.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q *
          (tangentIntervalReciprocalSieve P lo hi hP).nu q) =
        ∑ q ∈ P.divisors,
          tangentSelbergLambdaSquareCoefficient P R lambda q /
            (q : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      change tangentSelbergLambdaSquareCoefficient P R lambda q *
          tangentReciprocalArithmeticFunction q = _
      rw [tangentReciprocalArithmeticFunction_apply_of_pos
        (Nat.pos_of_mem_divisors hq)]
      simp only [one_mul, div_eq_mul_inv]
    _ = _ := tangentSelbergLambdaSquare_mainQuadraticIdentity
      (Nat.pos_of_ne_zero hP.ne_zero) lambda

/-! ## Gcd--totient diagonalization -/

/-- The reciprocal lcm kernel is the totient sum over common divisors. -/
theorem tangent_reciprocal_lcm_eq_totient_commonDivisorSum
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    1 / (Nat.lcm d e : ℝ) =
      ∑ r ∈ (Nat.gcd d e).divisors,
        (r.totient : ℝ) / ((d : ℝ) * (e : ℝ)) := by
  have hgcdPos : 0 < Nat.gcd d e := by positivity
  have hlcmPos : 0 < Nat.lcm d e := Nat.lcm_pos hd he
  have hidentity :
      (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) =
        (d : ℝ) * (e : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have htotient :
      (∑ r ∈ (Nat.gcd d e).divisors, (r.totient : ℝ)) =
        (Nat.gcd d e : ℝ) := by
    exact_mod_cast Nat.sum_totient (Nat.gcd d e)
  calc
    1 / (Nat.lcm d e : ℝ) =
        (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      have heReal : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
      have hlcmReal : (Nat.lcm d e : ℝ) ≠ 0 := by
        exact_mod_cast hlcmPos.ne'
      field_simp [hdReal, heReal, hlcmReal]
      nlinarith [hidentity]
    _ = (∑ r ∈ (Nat.gcd d e).divisors, (r.totient : ℝ)) /
          ((d : ℝ) * (e : ℝ)) := by rw [htotient]
    _ = ∑ r ∈ (Nat.gcd d e).divisors,
        (r.totient : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      rw [Finset.sum_div]

/-- Common divisors of two divisors of `P` can be summed over all divisors
of `P` using a literal indicator. -/
theorem tangent_reciprocal_lcm_eq_totient_modulusSum
    {P d e : ℕ} (hP : 0 < P)
    (hd : d ∈ P.divisors) (he : e ∈ P.divisors) :
    1 / (Nat.lcm d e : ℝ) =
      ∑ r ∈ P.divisors,
        if r ∣ d ∧ r ∣ e then
          (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
        else 0 := by
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hePos : 0 < e := Nat.pos_of_mem_divisors he
  have hgcdPos : 0 < Nat.gcd d e := by positivity
  have hdP : d ∣ P := (Nat.mem_divisors.mp hd).1
  have hfilter :
      P.divisors.filter (fun r ↦ r ∣ d ∧ r ∣ e) =
        (Nat.gcd d e).divisors := by
    ext r
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_hrP, _hP0⟩, hrd, hre⟩
      exact ⟨Nat.dvd_gcd hrd hre, hgcdPos.ne'⟩
    · rintro ⟨hrgcd, _hgcd0⟩
      have hrCommon := Nat.dvd_gcd_iff.mp hrgcd
      exact ⟨⟨hrCommon.1.trans hdP, hP.ne'⟩,
        hrCommon.1, hrCommon.2⟩
  rw [← Finset.sum_filter, hfilter]
  exact tangent_reciprocal_lcm_eq_totient_commonDivisorSum hdPos hePos



/-- Exact diagonalization of the finite Selberg quadratic form:

`Q(lambda) = sum_{r|P} phi(r) * y_r^2`.
-/
theorem tangentSelbergLambdaSquare_quadraticDiagonalization
    {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
      ∑ e ∈ tangentSelbergLambdaSupport P R,
        lambda d * lambda e / (Nat.lcm d e : ℝ)) =
      ∑ r ∈ P.divisors, (r.totient : ℝ) *
        tangentSelbergDiagonalTransform P R lambda r ^ 2 := by
  classical
  let S := tangentSelbergLambdaSupport P R
  calc
    (∑ d ∈ S, ∑ e ∈ S,
        lambda d * lambda e / (Nat.lcm d e : ℝ)) =
        ∑ d ∈ S, ∑ e ∈ S,
          lambda d * lambda e *
            (∑ r ∈ P.divisors,
              if r ∣ d ∧ r ∣ e then
                (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
              else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      calc
        lambda d * lambda e / (Nat.lcm d e : ℝ) =
            lambda d * lambda e *
              (1 / (Nat.lcm d e : ℝ)) := by ring
        _ = lambda d * lambda e *
            (∑ r ∈ P.divisors,
              if r ∣ d ∧ r ∣ e then
                (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
              else 0) := by
          rw [tangent_reciprocal_lcm_eq_totient_modulusSum hP
            (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp he).1]
    _ = ∑ d ∈ S, ∑ e ∈ S, ∑ r ∈ P.divisors,
        lambda d * lambda e *
          (if r ∣ d ∧ r ∣ e then
            (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
          else 0) := by
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.mul_sum]
    _ = ∑ r ∈ P.divisors, ∑ d ∈ S, ∑ e ∈ S,
        lambda d * lambda e *
          (if r ∣ d ∧ r ∣ e then
            (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
          else 0) := by
      calc
        (∑ d ∈ S, ∑ e ∈ S, ∑ r ∈ P.divisors,
            lambda d * lambda e *
              (if r ∣ d ∧ r ∣ e then
                (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
              else 0)) =
            ∑ d ∈ S, ∑ r ∈ P.divisors, ∑ e ∈ S,
              lambda d * lambda e *
                (if r ∣ d ∧ r ∣ e then
                  (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
                else 0) := by
          apply Finset.sum_congr rfl
          intro d _hd
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ r ∈ P.divisors, (r.totient : ℝ) *
        tangentSelbergDiagonalTransform P R lambda r ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [tangentSelbergDiagonalTransform, pow_two,
        Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hdPos := tangentSelbergLambdaSupport_pos hd
      have hePos := tangentSelbergLambdaSupport_pos he
      have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
      have heReal : (e : ℝ) ≠ 0 := by exact_mod_cast hePos.ne'
      by_cases hrd : r ∣ d <;> by_cases hre : r ∣ e
      · simp only [hrd, hre, and_self, if_true]
        field_simp [hdReal, heReal]
      · simp [hrd, hre]
      · simp [hrd, hre]
      · simp [hrd, hre]



/-! ## Finite upper-divisibility Mobius inversion -/

/-- The Mobius sum over the divisors of `n` which are multiples of `a` is
the Kronecker delta at `n=a`.  This is the one-variable identity needed for
upper-divisibility Mobius inversion on the truncated divisor support. -/
theorem tangent_sum_moebius_quotients_over_divisors
    {a n : ℕ} (ha : 0 < a) (hn : 0 < n) :
    (∑ d ∈ n.divisors,
        if a ∣ d then
          (ArithmeticFunction.moebius (n / d) : ℝ)
        else 0) = if n = a then 1 else 0 := by
  classical
  by_cases han : a ∣ n
  · have haLeN : a ≤ n := Nat.le_of_dvd hn han
    have hquotPos : 0 < n / a := Nat.div_pos haLeN ha
    rw [← Finset.sum_filter]
    calc
      (∑ d ∈ n.divisors.filter (fun d ↦ a ∣ d),
          (ArithmeticFunction.moebius (n / d) : ℝ)) =
          ∑ k ∈ (n / a).divisors,
            (ArithmeticFunction.moebius ((n / a) / k) : ℝ) := by
        symm
        apply Finset.sum_bij (fun k _hk ↦ a * k)
        · intro k hk
          have hkData := Nat.mem_divisors.mp hk
          exact Finset.mem_filter.mpr ⟨
            Nat.mem_divisors.mpr ⟨
              (Nat.dvd_div_iff_mul_dvd han).mp hkData.1,
              hn.ne'⟩,
            Nat.dvd_mul_right a k⟩
        · intro k₁ _hk₁ k₂ _hk₂ hmul
          exact Nat.mul_left_cancel ha hmul
        · intro d hd
          have hdData := Finset.mem_filter.mp hd
          have hdDivN := (Nat.mem_divisors.mp hdData.1).1
          refine ⟨d / a, ?_, Nat.mul_div_cancel' hdData.2⟩
          apply Nat.mem_divisors.mpr
          refine ⟨?_, hquotPos.ne'⟩
          apply (Nat.dvd_div_iff_mul_dvd han).mpr
          simpa only [Nat.mul_div_cancel' hdData.2] using hdDivN
        · intro k _hk
          rw [Nat.div_div_eq_div_mul]
      _ = ∑ k ∈ (n / a).divisors,
          (ArithmeticFunction.moebius k : ℝ) := by
        rw [← Nat.sum_divisorsAntidiagonal'
            (fun x _y ↦ (ArithmeticFunction.moebius x : ℝ)),
          Nat.sum_divisorsAntidiagonal
            (fun x _y ↦ (ArithmeticFunction.moebius x : ℝ))]
      _ = if n / a = 1 then 1 else 0 := by
        exact_mod_cast
          (Erdos390.Full.HeadPattern.Pattern.sum_moebius_divisors
            (a := n / a))
      _ = if n = a then 1 else 0 := by
        by_cases hna : n = a
        · subst n
          rw [Nat.div_self ha]
          simp
        · have hquotNe : n / a ≠ 1 := by
            intro hquot
            exact hna
              (Nat.eq_of_dvd_of_div_eq_one han hquot).symm
          simp [hna, hquotNe]
  · have hna : n ≠ a := by
      intro h
      subst n
      exact han (Nat.dvd_refl a)
    rw [if_neg hna]
    apply Finset.sum_eq_zero
    intro d hd
    have hdDivN := (Nat.mem_divisors.mp hd).1
    have had : ¬a ∣ d := by
      intro had
      exact han (had.trans hdDivN)
    simp [had]

/-- Mobius inversion for sums over multiples inside the downward-closed
finite support `S(P,R)`.  This is the exact inverse relation used by the
canonical Selberg coefficients below. -/
theorem tangentSelberg_upper_moebius_inversion
    {P R t : ℕ} (ht : t ∈ tangentSelbergLambdaSupport P R)
    (F : ℕ → ℝ) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        if t ∣ d then
          ∑ r ∈ tangentSelbergLambdaSupport P R,
            if d ∣ r then
              (ArithmeticFunction.moebius (r / d) : ℝ) * F r
            else 0
        else 0) = F t := by
  classical
  let S := tangentSelbergLambdaSupport P R
  have htPos := tangentSelbergLambdaSupport_pos ht
  change
    (∑ d ∈ S, if t ∣ d then
      ∑ r ∈ S, if d ∣ r then
        (ArithmeticFunction.moebius (r / d) : ℝ) * F r else 0
      else 0) = F t
  calc
    (∑ d ∈ S, if t ∣ d then
      ∑ r ∈ S, if d ∣ r then
        (ArithmeticFunction.moebius (r / d) : ℝ) * F r else 0
      else 0) =
        ∑ d ∈ S, ∑ r ∈ S,
          if t ∣ d ∧ d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) * F r
          else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases htd : t ∣ d
      · simp only [htd, true_and, if_true]
      · simp [htd]
    _ = ∑ r ∈ S, ∑ d ∈ S,
        if t ∣ d ∧ d ∣ r then
          (ArithmeticFunction.moebius (r / d) : ℝ) * F r
        else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ S, F r *
        (∑ d ∈ S, if t ∣ d ∧ d ∣ r then
          (ArithmeticFunction.moebius (r / d) : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases htd : t ∣ d <;> by_cases hdr : d ∣ r <;>
        simp [htd, hdr, mul_comm]
    _ = ∑ r ∈ S, F r * (if r = t then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      have hrData := mem_tangentSelbergLambdaSupport.mp hr
      have hrPos := tangentSelbergLambdaSupport_pos hr
      have hfilter : S.filter (fun d ↦ d ∣ r) = r.divisors := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨_hdS, hdr⟩
          exact ⟨hdr, hrPos.ne'⟩
        · rintro ⟨hdr, _hr0⟩
          have hdLeR : d ≤ R :=
            (Nat.le_of_dvd hrPos hdr).trans hrData.2
          exact ⟨mem_tangentSelbergLambdaSupport.mpr
            ⟨⟨hdr.trans hrData.1.1, hrData.1.2⟩, hdLeR⟩, hdr⟩
      calc
        (∑ d ∈ S, if t ∣ d ∧ d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) else 0) =
            ∑ d ∈ S.filter (fun d ↦ d ∣ r),
              if t ∣ d then
                (ArithmeticFunction.moebius (r / d) : ℝ)
              else 0 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro d _hd
          by_cases htd : t ∣ d <;> by_cases hdr : d ∣ r <;>
            simp [htd, hdr]
        _ = ∑ d ∈ r.divisors,
              if t ∣ d then
                (ArithmeticFunction.moebius (r / d) : ℝ)
              else 0 := by rw [hfilter]
        _ = if r = t then 1 else 0 :=
          tangent_sum_moebius_quotients_over_divisors htPos hrPos
    _ = F t := by
      have htS : t ∈ S := ht
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
      rw [if_pos htS]



theorem tangentSelbergDensitySum_pos
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    0 < tangentSelbergDensitySum P R := by
  have hOneMem := one_mem_tangentSelbergLambdaSupport hP hR
  have htermNonneg : ∀ r ∈ tangentSelbergLambdaSupport P R,
      0 ≤ (ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ) := by
    intro r hr
    have hrPos := tangentSelbergLambdaSupport_pos hr
    have htotientPos : (0 : ℝ) < (r.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hrPos
    exact div_nonneg (sq_nonneg _) htotientPos.le
  calc
    0 < (1 : ℝ) := zero_lt_one
    _ = (ArithmeticFunction.moebius 1 : ℝ) ^ 2 /
        ((1 : ℕ).totient : ℝ) := by norm_num
    _ ≤ tangentSelbergDensitySum P R := by
      exact Finset.single_le_sum htermNonneg hOneMem



/-! ## Sharp finite coefficient norm -/

/-- Grouping pairs by lcm loses at most the triangle inequality: the full
coefficient `l1` norm is bounded by the square of the Lambda `l1` norm. -/
theorem tangentSelbergLambdaSquareCoefficient_l1_le
    {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) :
    (∑ q ∈ P.divisors,
        |tangentSelbergLambdaSquareCoefficient P R lambda q|) ≤
      (∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d|) ^ 2 := by
  classical
  let S := tangentSelbergLambdaSupport P R
  calc
    (∑ q ∈ P.divisors,
        |tangentSelbergLambdaSquareCoefficient P R lambda q|) ≤
        ∑ q ∈ P.divisors, ∑ d ∈ S, ∑ e ∈ S,
          |if Nat.lcm d e = q then lambda d * lambda e else 0| := by
      apply Finset.sum_le_sum
      intro q _hq
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun d _hd ↦
          Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ d ∈ S, ∑ e ∈ S, |lambda d * lambda e| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      have hdP : d ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      have heP : e ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
      have hlcmMem : Nat.lcm d e ∈ P.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.lcm_dvd hdP heP, hP.ne'⟩
      rw [Finset.sum_eq_single (Nat.lcm d e)]
      · rw [if_pos rfl, abs_mul]
      · intro q _hq hqNe
        rw [if_neg hqNe.symm, abs_zero]
      · exact fun hnotMem ↦ (hnotMem hlcmMem).elim
    _ = (∑ d ∈ S, |lambda d|) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      exact abs_mul (lambda d) (lambda e)

/-! ## A concrete interval upper sieve -/

/-- Concrete Lambda-squared interval theorem.  Its main term is the exact
quadratic form and its endpoint error is the square of the Lambda `l1`
norm. -/
theorem reducedResidueIoc_card_le_lambdaSquare
    {P R lo hi : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) *
          (∑ d ∈ tangentSelbergLambdaSupport P R,
            ∑ e ∈ tangentSelbergLambdaSupport P R,
              lambda d * lambda e / (Nat.lcm d e : ℝ)) +
        (∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d|) ^ 2 := by
  have hPPos : 0 < P := Nat.pos_of_ne_zero hP.ne_zero
  have hupper := reducedResidueIoc_card_le_abstractSelberg_l1
    (lo := lo) (hi := hi) hP
    (tangentSelbergLambdaSquareCoefficient P R lambda)
    (tangentSelbergLambdaSquareCoefficient_isUpperMoebius
      hPPos hR lambda hlambdaOne)
  rw [tangentIntervalReciprocalSieve_lambdaSquare_mainSum hP lambda] at hupper
  exact hupper.trans (add_le_add_right
    (tangentSelbergLambdaSquareCoefficient_l1_le hPPos lambda) _)

/-- Explicit coefficient-estimate interface.  Bounds for the quadratic form
and Lambda norm immediately give the classical two-term Selberg shape,
with no loss in either displayed constant. -/
theorem reducedResidueIoc_card_le_lambdaSquare_of_bounds
    {P R lo hi : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1)
    {mainBound lambdaBound : ℝ}
    (hmain :
      (∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e / (Nat.lcm d e : ℝ)) ≤ mainBound)
    (hlambda :
      (∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d|) ≤
        lambdaBound) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) * mainBound + lambdaBound ^ 2 := by
  have hraw := reducedResidueIoc_card_le_lambdaSquare
    (lo := lo) (hi := hi) hP hR lambda hlambdaOne
  have hlength : (0 : ℝ) ≤ ((hi - lo : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlambdaNonneg :
      0 ≤ ∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d| :=
    Finset.sum_nonneg fun d _hd ↦ abs_nonneg (lambda d)
  have hlambdaBoundNonneg : 0 ≤ lambdaBound :=
    hlambdaNonneg.trans hlambda
  have hsquare :
      (∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d|) ^ 2 ≤
        lambdaBound ^ 2 := by
    nlinarith
  exact hraw.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmain hlength) hsquare)

/-- Paper-level specialization `R=y^2`, so the squared coefficient bound
has exactly the `y^4/(log y)^2` scale. -/
theorem reducedResidueIoc_card_le_lambdaSquare_paperShape
    {P lo hi y : ℕ} (hP : Squarefree P) (hy : 1 ≤ y)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1)
    {Cmain Clambda : ℝ}
    (hmain :
      (∑ d ∈ tangentSelbergLambdaSupport P (y ^ 2),
        ∑ e ∈ tangentSelbergLambdaSupport P (y ^ 2),
          lambda d * lambda e / (Nat.lcm d e : ℝ)) ≤
        Cmain / Real.log (y : ℝ))
    (hlambda :
      (∑ d ∈ tangentSelbergLambdaSupport P (y ^ 2), |lambda d|) ≤
        Clambda * (y : ℝ) ^ 2 / Real.log (y : ℝ)) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) * (Cmain / Real.log (y : ℝ)) +
        Clambda ^ 2 * (y : ℝ) ^ 4 / Real.log (y : ℝ) ^ 2 := by
  have h := reducedResidueIoc_card_le_lambdaSquare_of_bounds
    (lo := lo) (hi := hi) hP (one_le_pow₀ hy) lambda hlambdaOne
      hmain hlambda
  calc
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
        ((hi - lo : ℕ) : ℝ) * (Cmain / Real.log (y : ℝ)) +
          (Clambda * (y : ℝ) ^ 2 / Real.log (y : ℝ)) ^ 2 := h
    _ = ((hi - lo : ℕ) : ℝ) * (Cmain / Real.log (y : ℝ)) +
        Clambda ^ 2 * (y : ℝ) ^ 4 / Real.log (y : ℝ) ^ 2 := by ring

/-! ## Canonical finite Selberg weights -/



/-- On its finite support, division by the index exposes the literal upper
Mobius inverse used to define the canonical weight. -/
theorem tangentSelbergCanonicalLambda_div
    {P R d : ℕ} (_hP : 0 < P) (_hR : 1 ≤ R)
    (hd : d ∈ tangentSelbergLambdaSupport P R) :
    tangentSelbergCanonicalLambda P R d / (d : ℝ) =
      (1 / tangentSelbergDensitySum P R) *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          if d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) *
              ((ArithmeticFunction.moebius r : ℝ) / (r.totient : ℝ))
          else 0 := by
  have hdPos := tangentSelbergLambdaSupport_pos hd
  have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
  rw [tangentSelbergCanonicalLambda, if_pos hd]
  calc
    ((d : ℝ) / tangentSelbergDensitySum P R *
        (∑ r ∈ tangentSelbergLambdaSupport P R,
          if d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) *
                (ArithmeticFunction.moebius r : ℝ) /
              (r.totient : ℝ)
          else 0)) / (d : ℝ) =
        (1 / tangentSelbergDensitySum P R) *
          (∑ r ∈ tangentSelbergLambdaSupport P R,
            if d ∣ r then
              (ArithmeticFunction.moebius (r / d) : ℝ) *
                  (ArithmeticFunction.moebius r : ℝ) /
                (r.totient : ℝ)
            else 0) := by
      rw [div_eq_mul_inv]
      have hcancel : (d : ℝ) * (d : ℝ)⁻¹ = 1 :=
        mul_inv_cancel₀ hdReal
      calc
        ((d : ℝ) / tangentSelbergDensitySum P R *
            (∑ r ∈ tangentSelbergLambdaSupport P R,
              if d ∣ r then
                (ArithmeticFunction.moebius (r / d) : ℝ) *
                    (ArithmeticFunction.moebius r : ℝ) /
                  (r.totient : ℝ)
              else 0)) * (d : ℝ)⁻¹ =
            ((d : ℝ) * (d : ℝ)⁻¹) *
              (1 / tangentSelbergDensitySum P R) *
                (∑ r ∈ tangentSelbergLambdaSupport P R,
                  if d ∣ r then
                    (ArithmeticFunction.moebius (r / d) : ℝ) *
                        (ArithmeticFunction.moebius r : ℝ) /
                      (r.totient : ℝ)
                  else 0) := by ring
        _ = _ := by rw [hcancel, one_mul]
    _ = (1 / tangentSelbergDensitySum P R) *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          if d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) *
              ((ArithmeticFunction.moebius r : ℝ) / (r.totient : ℝ))
          else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hdr : d ∣ r
      · simp only [hdr, if_true]
        ring
      · simp [hdr]

/-- The diagonal transform of the canonical weight equals the target
`mu(t)/(phi(t) G)` at every retained divisor. -/
theorem tangentSelbergCanonicalLambda_diagonalTransform_of_mem
    {P R t : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (ht : t ∈ tangentSelbergLambdaSupport P R) :
    tangentSelbergDiagonalTransform P R
        (tangentSelbergCanonicalLambda P R) t =
      (ArithmeticFunction.moebius t : ℝ) /
        ((t.totient : ℝ) * tangentSelbergDensitySum P R) := by
  let S := tangentSelbergLambdaSupport P R
  let F : ℕ → ℝ := fun r ↦
    (ArithmeticFunction.moebius r : ℝ) / (r.totient : ℝ)
  have hinversion := tangentSelberg_upper_moebius_inversion ht F
  rw [tangentSelbergDiagonalTransform]
  change
    (∑ d ∈ S, if t ∣ d then
      tangentSelbergCanonicalLambda P R d / (d : ℝ) else 0) = _
  calc
    (∑ d ∈ S, if t ∣ d then
      tangentSelbergCanonicalLambda P R d / (d : ℝ) else 0) =
        (1 / tangentSelbergDensitySum P R) *
          (∑ d ∈ S, if t ∣ d then
            ∑ r ∈ S, if d ∣ r then
              (ArithmeticFunction.moebius (r / d) : ℝ) * F r
            else 0
          else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases htd : t ∣ d
      · simp only [htd, if_true]
        exact tangentSelbergCanonicalLambda_div hP hR hd
      · simp [htd]
    _ = (1 / tangentSelbergDensitySum P R) * F t := by
      rw [hinversion]
    _ = (ArithmeticFunction.moebius t : ℝ) /
        ((t.totient : ℝ) * tangentSelbergDensitySum P R) := by
      dsimp only [F]
      ring

/-- Total form of the canonical diagonal target.  Outside the level
support the transform vanishes because a divisor of a retained index is
itself retained. -/
theorem tangentSelbergCanonicalLambda_diagonalTransform
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) (t : ℕ) :
    tangentSelbergDiagonalTransform P R
        (tangentSelbergCanonicalLambda P R) t =
      if t ∈ tangentSelbergLambdaSupport P R then
        (ArithmeticFunction.moebius t : ℝ) /
          ((t.totient : ℝ) * tangentSelbergDensitySum P R)
      else 0 := by
  by_cases ht : t ∈ tangentSelbergLambdaSupport P R
  · rw [if_pos ht]
    exact tangentSelbergCanonicalLambda_diagonalTransform_of_mem
      hP hR ht
  · rw [if_neg ht, tangentSelbergDiagonalTransform]
    apply Finset.sum_eq_zero
    intro d hd
    have hdData := mem_tangentSelbergLambdaSupport.mp hd
    have hdPos := tangentSelbergLambdaSupport_pos hd
    have hnotDvd : ¬t ∣ d := by
      intro htd
      have htLeR : t ≤ R :=
        (Nat.le_of_dvd hdPos htd).trans hdData.2
      exact ht (mem_tangentSelbergLambdaSupport.mpr
        ⟨⟨htd.trans hdData.1.1, hdData.1.2⟩, htLeR⟩)
    simp [hnotDvd]

/-- Exact finite optimization identity for the canonical Selberg weights:
their quadratic main term attains the Cauchy--Schwarz lower bound `1/G`. -/
theorem tangentSelbergCanonicalLambda_quadratic_eq_invDensity
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
      ∑ e ∈ tangentSelbergLambdaSupport P R,
        tangentSelbergCanonicalLambda P R d *
            tangentSelbergCanonicalLambda P R e /
          (Nat.lcm d e : ℝ)) =
      1 / tangentSelbergDensitySum P R := by
  classical
  let S := tangentSelbergLambdaSupport P R
  have hGNe : tangentSelbergDensitySum P R ≠ 0 :=
    (tangentSelbergDensitySum_pos hP hR).ne'
  have hsubset : S ⊆ P.divisors := Finset.filter_subset _ _
  have hfilter : P.divisors.filter (fun r ↦ r ∈ S) = S := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · exact fun hr ↦ hr.2
    · exact fun hr ↦ ⟨hsubset hr, hr⟩
  rw [tangentSelbergLambdaSquare_quadraticDiagonalization hP]
  calc
    (∑ r ∈ P.divisors, (r.totient : ℝ) *
        tangentSelbergDiagonalTransform P R
          (tangentSelbergCanonicalLambda P R) r ^ 2) =
        ∑ r ∈ P.divisors,
          if r ∈ S then
            (r.totient : ℝ) *
              ((ArithmeticFunction.moebius r : ℝ) /
                ((r.totient : ℝ) * tangentSelbergDensitySum P R)) ^ 2
          else 0 := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [tangentSelbergCanonicalLambda_diagonalTransform hP hR]
      by_cases hrS : r ∈ S <;> simp [S, hrS]
    _ = ∑ r ∈ S, (r.totient : ℝ) *
        ((ArithmeticFunction.moebius r : ℝ) /
          ((r.totient : ℝ) * tangentSelbergDensitySum P R)) ^ 2 := by
      rw [← Finset.sum_filter, hfilter]
    _ = ∑ r ∈ S,
        (1 / tangentSelbergDensitySum P R ^ 2) *
          ((ArithmeticFunction.moebius r : ℝ) ^ 2 /
            (r.totient : ℝ)) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrPos := tangentSelbergLambdaSupport_pos hr
      have htotientNe : (r.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hrPos).ne'
      field_simp [htotientNe, hGNe]
    _ = (1 / tangentSelbergDensitySum P R ^ 2) *
        (∑ r ∈ S,
          (ArithmeticFunction.moebius r : ℝ) ^ 2 /
            (r.totient : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (1 / tangentSelbergDensitySum P R ^ 2) *
        tangentSelbergDensitySum P R := by
      change
        (1 / tangentSelbergDensitySum P R ^ 2) *
            tangentSelbergDensitySum P R =
          (1 / tangentSelbergDensitySum P R ^ 2) *
            tangentSelbergDensitySum P R
      rfl
    _ = 1 / tangentSelbergDensitySum P R := by
      field_simp [hGNe]

/-- The canonical finite weights have the normalization required by the
Lambda-squared majorant. -/
theorem tangentSelbergCanonicalLambda_one
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    tangentSelbergCanonicalLambda P R 1 = 1 := by
  have hOneMem := one_mem_tangentSelbergLambdaSupport hP hR
  have hGNe : tangentSelbergDensitySum P R ≠ 0 :=
    (tangentSelbergDensitySum_pos hP hR).ne'
  rw [tangentSelbergCanonicalLambda, if_pos hOneMem]
  have hsum :
      (∑ r ∈ tangentSelbergLambdaSupport P R,
        if 1 ∣ r then
          (ArithmeticFunction.moebius (r / 1) : ℝ) *
              (ArithmeticFunction.moebius r : ℝ) /
            (r.totient : ℝ)
        else 0) = tangentSelbergDensitySum P R := by
    rw [tangentSelbergDensitySum]
    apply Finset.sum_congr rfl
    intro r _hr
    simp only [one_dvd, if_true, Nat.div_one]
    ring
  rw [hsum]
  field_simp [hGNe]
  norm_num







/-- Canonical `R=y^2` specialization.  Supplying the two remaining
analytic estimates gives exactly the paper's
`H/log y + y^4/(log y)^2` shape. -/
theorem reducedResidueIoc_card_le_canonicalLambdaSquare_paperShape
    {P lo hi y : ℕ} (hP : Squarefree P) (hy : 1 ≤ y)
    {Cmain Clambda : ℝ}
    (hdensity :
      1 / tangentSelbergDensitySum P (y ^ 2) ≤
        Cmain / Real.log (y : ℝ))
    (hlambda :
      (∑ d ∈ tangentSelbergLambdaSupport P (y ^ 2),
        |tangentSelbergCanonicalLambda P (y ^ 2) d|) ≤
          Clambda * (y : ℝ) ^ 2 / Real.log (y : ℝ)) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) * (Cmain / Real.log (y : ℝ)) +
        Clambda ^ 2 * (y : ℝ) ^ 4 / Real.log (y : ℝ) ^ 2 := by
  apply reducedResidueIoc_card_le_lambdaSquare_paperShape
    hP hy (tangentSelbergCanonicalLambda P (y ^ 2))
      (tangentSelbergCanonicalLambda_one
        (Nat.pos_of_ne_zero hP.ne_zero) (one_le_pow₀ hy))
  · rw [tangentSelbergCanonicalLambda_quadratic_eq_invDensity
      (Nat.pos_of_ne_zero hP.ne_zero) (one_le_pow₀ hy)]
    exact hdensity
  · exact hlambda

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentExceptionalCanonicalBounds -/
section


/-!
# Analytic bounds for the canonical exceptional-row Lambda-squared sieve

This file closes the two analytic inputs left open by
`TangentExceptionalLambdaSquareSieve`.  The constants are deliberately
coarse and fixed.  The PNT error constant and cutoff inherited from
`PrimeBandQuadrature` are named noncomputable choices, rather than numerical
values.  The proof has three ingredients.

* The verified interval Mertens theorem in `Full.PrimeBandQuadrature`
  gives a lower bound for the Euler product
  `prod_{p <= y} (1 + 1/(p-1))`.
* A logarithmic first-moment argument shows that truncating the squarefree
  divisor sum at `y^2` retains at least one tenth of that Euler product.
* A nonnegative Dirichlet-convolution majorant bounds the canonical
  Lambda `l1` norm by `exp 4 * y^2 / G`.

Thus the only constants in the final result are a named finite Mertens
loss, `10 * exp(loss)` for the main term, and an additional factor `exp 4`
for the Lambda norm.  No prime-product or coefficient estimate is assumed.
-/

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.sigma ArithmeticFunction.zeta
open Filter Set Topology

namespace Erdos390.WholePaper

noncomputable section

open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

/-! ## Multiplicative functions used in the Euler-product ledgers -/



theorem tangentReciprocalTotientArithmeticFunction_isMultiplicative :
    tangentReciprocalTotientArithmeticFunction.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [tangentReciprocalTotientArithmeticFunction], ?_⟩
  intro m n hm hn hmn
  simp only [tangentReciprocalTotientArithmeticFunction,
    ArithmeticFunction.coe_mk, hm, hn, mul_ne_zero hm hn, if_false,
    Nat.totient_mul hmn, Nat.cast_mul]
  field_simp







theorem tangentSigmaTotientRatioArithmeticFunction_isMultiplicative :
    tangentSigmaTotientRatioArithmeticFunction.IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_sigma.natCast).pmul
    tangentReciprocalTotientArithmeticFunction_isMultiplicative





theorem tangentSquarefreeFourOverPrimeArithmeticFunction_isMultiplicative :
    tangentSquarefreeFourOverPrimeArithmeticFunction.IsMultiplicative :=
  ((ArithmeticFunction.isMultiplicative_moebius.intCast.pmul
      ArithmeticFunction.isMultiplicative_moebius.intCast).pmul
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors
      (fun p ↦ 4 / (p : ℝ))))

theorem tangentSquarefreeFourOverPrimeArithmeticFunction_nonneg
    (n : ℕ) :
    0 ≤ tangentSquarefreeFourOverPrimeArithmeticFunction n := by
  rw [tangentSquarefreeFourOverPrimeArithmeticFunction,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  have hprod :
      0 ≤ (ArithmeticFunction.prodPrimeFactors
        (fun p ↦ 4 / (p : ℝ))) n := by
    by_cases hn : n = 0
    · subst n
      simp [ArithmeticFunction.prodPrimeFactors]
    · rw [ArithmeticFunction.prodPrimeFactors_apply hn]
      exact Finset.prod_nonneg fun p _hp ↦ by positivity
  exact mul_nonneg (mul_self_nonneg _) hprod



theorem tangentSquarefreeFourOverPrimeArithmeticFunction_eq_zero_of_not_squarefree
    {n : ℕ} (hn : ¬Squarefree n) :
    tangentSquarefreeFourOverPrimeArithmeticFunction n = 0 := by
  rw [tangentSquarefreeFourOverPrimeArithmeticFunction,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]



theorem tangentSquarefreeFourOverSquareArithmeticFunction_isMultiplicative :
    tangentSquarefreeFourOverSquareArithmeticFunction.IsMultiplicative :=
  tangentSquarefreeFourOverPrimeArithmeticFunction_isMultiplicative.pmul
    tangentReciprocalArithmeticFunction_isMultiplicative

theorem tangentSquarefreeFourOverSquareArithmeticFunction_nonneg
    (n : ℕ) :
    0 ≤ tangentSquarefreeFourOverSquareArithmeticFunction n := by
  rw [tangentSquarefreeFourOverSquareArithmeticFunction,
    ArithmeticFunction.pmul_apply]
  exact mul_nonneg
    (tangentSquarefreeFourOverPrimeArithmeticFunction_nonneg n)
    (by
      by_cases hn : n = 0
      · subst n
        simp [tangentReciprocalArithmeticFunction]
      · simp [tangentReciprocalArithmeticFunction, hn])



/-! ## Full density and logarithmic first moment -/





theorem tangentSelbergFullDensitySum_eq_primeProduct
    {P : ℕ} (hP : Squarefree P) :
    tangentSelbergFullDensitySum P =
      ∏ p ∈ P.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
  have hEuler :=
    tangentReciprocalTotientArithmeticFunction_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
      hP
  rw [tangentSelbergFullDensitySum]
  symm
  calc
    (∏ p ∈ P.primeFactors, (1 + 1 / ((p : ℝ) - 1))) =
        ∏ p ∈ P.primeFactors,
          (1 + tangentReciprocalTotientArithmeticFunction p) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [tangentReciprocalTotientArithmeticFunction_apply_prime
        (Nat.prime_of_mem_primeFactors hp)]
    _ = ∑ r ∈ P.divisors,
        tangentReciprocalTotientArithmeticFunction r := hEuler
    _ = ∑ r ∈ P.divisors, 1 / (r.totient : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [tangentReciprocalTotientArithmeticFunction_apply_of_pos
        (Nat.pos_of_mem_divisors hr)]

theorem tangentSelbergDensitySum_eq_reciprocalTotient
    {P R : ℕ} (hP : Squarefree P) :
    tangentSelbergDensitySum P R =
      ∑ r ∈ tangentSelbergLambdaSupport P R,
        1 / (r.totient : ℝ) := by
  rw [tangentSelbergDensitySum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrData := mem_tangentSelbergLambdaSupport.mp hr
  have hrsq : Squarefree r :=
    hP.squarefree_of_dvd hrData.1.1
  have hmuZ := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hrsq
  have hmuR : (ArithmeticFunction.moebius r : ℝ) ^ 2 = 1 := by
    exact_mod_cast hmuZ
  rw [hmuR]

/-! A powerset moment inequality.  It is the finite probabilistic estimate
behind the truncation: the first moment of independent nonnegative local
weights is at most their partition function times `sum b_p a_p`. -/

theorem sum_powerset_sum_mul_prod_le
    {s : Finset ℕ} (a b : ℕ → ℝ)
    (ha : ∀ p ∈ s, 0 ≤ a p) (hb : ∀ p ∈ s, 0 ≤ b p) :
    (∑ t ∈ s.powerset,
        (∑ p ∈ t, b p) * ∏ p ∈ t, a p) ≤
      (∏ p ∈ s, (1 + a p)) * ∑ p ∈ s, b p * a p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hap : 0 ≤ a p := ha p (Finset.mem_insert_self p s)
      have hbp : 0 ≤ b p := hb p (Finset.mem_insert_self p s)
      have haS : ∀ q ∈ s, 0 ≤ a q := by
        intro q hq
        exact ha q (Finset.mem_insert_of_mem hq)
      have hbS : ∀ q ∈ s, 0 ≤ b q := by
        intro q hq
        exact hb q (Finset.mem_insert_of_mem hq)
      let M : ℝ := ∑ t ∈ s.powerset,
        (∑ q ∈ t, b q) * ∏ q ∈ t, a q
      let W : ℝ := ∏ q ∈ s, (1 + a q)
      let B : ℝ := ∑ q ∈ s, b q * a q
      have hM : M ≤ W * B := by
        simpa only [M, W, B] using ih haS hbS
      have hW : 0 ≤ W := by
        dsimp only [W]
        exact Finset.prod_nonneg fun q hq ↦ by
          exact add_nonneg zero_le_one (haS q hq)
      have hexpand :
          (∑ t ∈ (insert p s).powerset,
              (∑ q ∈ t, b q) * ∏ q ∈ t, a q) =
            M + a p * b p * W + a p * M := by
        have hinsert :
          (∑ t ∈ s.powerset,
              (∑ q ∈ insert p t, b q) *
                ∏ q ∈ insert p t, a q) =
            a p * b p * W + a p * M := by
          calc
            (∑ t ∈ s.powerset,
                (∑ q ∈ insert p t, b q) *
                  ∏ q ∈ insert p t, a q) =
                ∑ t ∈ s.powerset,
                  ((a p * b p) * (∏ q ∈ t, a q) +
                    a p * ((∑ q ∈ t, b q) * (∏ q ∈ t, a q))) := by
              apply Finset.sum_congr rfl
              intro t ht
              have hpt : p ∉ t :=
                Finset.notMem_of_mem_powerset_of_notMem ht hp
              rw [Finset.sum_insert hpt, Finset.prod_insert hpt]
              ring
            _ = a p * b p * W + a p * M := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum, ← Finset.prod_one_add]
        rw [Finset.sum_powerset_insert hp, hinsert]
        change M + (a p * b p * W + a p * M) =
          M + a p * b p * W + a p * M
        ring
      have hscaled : a p * M ≤ a p * (W * B) :=
        mul_le_mul_of_nonneg_left hM hap
      rw [hexpand, Finset.prod_insert hp, Finset.sum_insert hp]
      change M + a p * b p * W + a p * M ≤
        (1 + a p) * W * (b p * a p + B)
      nlinarith [hscaled,
        mul_nonneg hap (mul_nonneg hap (mul_nonneg hbp hW))]

theorem tangentSelbergFullLogMoment_le
    {P : ℕ} (hP : Squarefree P) :
    tangentSelbergFullLogMoment P ≤
      tangentSelbergFullDensitySum P *
        (∑ p ∈ P.primeFactors,
          Real.log (p : ℝ) / ((p : ℝ) - 1)) := by
  classical
  let a : ℕ → ℝ := fun p ↦ 1 / ((p : ℝ) - 1)
  let b : ℕ → ℝ := fun p ↦ Real.log (p : ℝ)
  have hprime (p : ℕ) (hp : p ∈ P.primeFactors) : p.Prime :=
    Nat.prime_of_mem_primeFactors hp
  have ha : ∀ p ∈ P.primeFactors, 0 ≤ a p := by
    intro p hp
    dsimp only [a]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (hprime p hp).two_le
    exact one_div_nonneg.mpr (by linarith)
  have hb : ∀ p ∈ P.primeFactors, 0 ≤ b p := by
    intro p hp
    dsimp only [b]
    exact Real.log_nonneg (by
      exact_mod_cast (hprime p hp).one_le)
  have hpowerset := sum_powerset_sum_mul_prod_le a b ha hb
  have hdivisors :
      tangentSelbergFullLogMoment P =
        ∑ t ∈ P.primeFactors.powerset,
          (∑ p ∈ t, b p) * ∏ p ∈ t, a p := by
    rw [tangentSelbergFullLogMoment,
      ← Nat.divisors_filter_squarefree_of_squarefree hP,
      Nat.sum_divisors_filter_squarefree hP.ne_zero]
    simp only [Nat.factors_eq]
    apply Finset.sum_congr rfl
    intro t ht
    rw [t.prod_val, Function.id_def]
    have htSub : t ⊆ P.primeFactors := Finset.mem_powerset.mp ht
    have htPrime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htSub hp)
    have hprodPos : 0 < ∏ p ∈ t, p :=
      Finset.prod_pos fun p hp ↦ (htPrime p hp).pos
    have hlog :
        Real.log ((∏ p ∈ t, p : ℕ) : ℝ) = ∑ p ∈ t, b p := by
      rw [Nat.cast_prod, Real.log_prod]
      intro p hp
      exact_mod_cast (htPrime p hp).ne_zero
    have hrecip :
        1 / (((∏ p ∈ t, p : ℕ).totient : ℕ) : ℝ) =
          ∏ p ∈ t, a p := by
      have hmap :=
        tangentReciprocalTotientArithmeticFunction_isMultiplicative.map_prod_of_prime
          t htPrime
      rw [tangentReciprocalTotientArithmeticFunction_apply_of_pos hprodPos]
        at hmap
      calc
        1 / (((∏ p ∈ t, p : ℕ).totient : ℕ) : ℝ) =
            ∏ p ∈ t,
              tangentReciprocalTotientArithmeticFunction p := hmap
        _ = ∏ p ∈ t, a p := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [tangentReciprocalTotientArithmeticFunction_apply_prime
            (htPrime p hp)]
    rw [hlog, div_eq_mul_inv]
    have hrecip' :
        ((((∏ p ∈ t, p : ℕ).totient : ℕ) : ℝ))⁻¹ =
          ∏ p ∈ t, a p := by
      simpa only [one_div] using hrecip
    rw [hrecip']
  have hdensity :
      tangentSelbergFullDensitySum P =
        ∏ p ∈ P.primeFactors, (1 + a p) := by
    simpa only [a] using tangentSelbergFullDensitySum_eq_primeProduct hP
  rw [hdivisors, hdensity]
  simpa only [a, b, div_eq_mul_inv, one_mul] using hpowerset

/-! ## Prime sums at the rough-head modulus -/

theorem roughHeadModulus_primeFactors (y : ℕ) :
    (roughHeadModulus y).primeFactors = primesUpTo y := by
  rw [roughHeadModulus]
  exact Nat.primeFactors_prod fun p hp ↦ (mem_primesUpTo.mp hp).1

theorem wholePaper_primesUpTo_eq_full_primesUpTo (y : ℕ) :
    primesUpTo y = Erdos390.Full.PrimeSums.primesUpTo y := by
  ext p
  simp [mem_primesUpTo, Erdos390.Full.PrimeSums.primesUpTo,
    and_comm]

theorem roughHead_primeFactor_logMoment_le_fullPrimeSums
    (y : ℕ) :
    (∑ p ∈ (roughHeadModulus y).primeFactors,
        Real.log (p : ℝ) / ((p : ℝ) - 1)) ≤
      fullLogReciprocalSum y + fullReciprocalSum y := by
  rw [roughHeadModulus_primeFactors,
    wholePaper_primesUpTo_eq_full_primesUpTo]
  rw [fullLogReciprocalSum, fullReciprocalSum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime : p.Prime := by
    have hpData : p ≤ y ∧ p.Prime := by
      simpa [Erdos390.Full.PrimeSums.primesUpTo] using hp
    exact hpData.2
  have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hpPredPos : (0 : ℝ) < (p : ℝ) - 1 := by
    have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hpPrime.two_le
    linarith
  have hlogLe : Real.log (p : ℝ) ≤ (p : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hpPos
  have hcorrection :
      Real.log (p : ℝ) /
          ((p : ℝ) * ((p : ℝ) - 1)) ≤
        1 / (p : ℝ) := by
    calc
      Real.log (p : ℝ) /
            ((p : ℝ) * ((p : ℝ) - 1)) =
          (Real.log (p : ℝ) / ((p : ℝ) - 1)) /
            (p : ℝ) := by
        field_simp [hpPos.ne', hpPredPos.ne']
      _ ≤ 1 / (p : ℝ) := by
        apply div_le_div_of_nonneg_right _ hpPos.le
        exact (div_le_one hpPredPos).2 hlogLe
  calc
    Real.log (p : ℝ) / ((p : ℝ) - 1) =
        Real.log (p : ℝ) / (p : ℝ) +
          Real.log (p : ℝ) /
            ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp [hpPos.ne', hpPredPos.ne']
      ring
    _ ≤ Real.log (p : ℝ) / (p : ℝ) + 1 / (p : ℝ) :=
      by
        simpa only [add_comm] using
          add_le_add_right hcorrection (Real.log (p : ℝ) / (p : ℝ))

/-- The elementary Chebyshev bounds already give the strict coefficient
needed for logarithmic truncation: eventually the `1/(p-1)` logarithmic
moment is at most `9/5 log y`. -/
theorem eventually_fullPrimeMoment_le_nine_fifths_log :
    ∀ᶠ y : ℕ in atTop,
      fullLogReciprocalSum y + fullReciprocalSum y ≤
        (9 / 5 : ℝ) * Real.log (y : ℝ) := by
  let L : ℕ → ℝ := fun y ↦ Real.log (y : ℝ)
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvL : Tendsto (fun y : ℕ ↦ 1 / L y) atTop (nhds 0) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    exact hone.div_atTop hLTop
  have hlogRatio :
      Tendsto (fun y : ℕ ↦ Real.log (L y) / L y)
        atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hmajor : Tendsto (fun y : ℕ ↦
      (2 * Real.log 4 + 3 * Real.log 4 *
        (Real.log (L y) - Real.log (Real.log 2))) / L y)
      atTop (nhds 0) := by
    have hzero : Tendsto (fun y : ℕ ↦
        (2 * Real.log 4) * (1 / L y) +
          (3 * Real.log 4) * (Real.log (L y) / L y) -
          (3 * Real.log 4 * Real.log (Real.log 2)) * (1 / L y))
        atTop (nhds 0) := by
      simpa only [mul_zero, add_zero, sub_zero] using
        ((tendsto_const_nhds.mul hinvL).add
          (tendsto_const_nhds.mul hlogRatio)).sub
            (tendsto_const_nhds.mul hinvL)
    apply hzero.congr'
    filter_upwards with y
    ring
  have hmajorSmall : ∀ᶠ y : ℕ in atTop,
      (2 * Real.log 4 + 3 * Real.log 4 *
        (Real.log (L y) - Real.log (Real.log 2))) / L y ≤
        (1 / 5 : ℝ) :=
    hmajor.eventually (eventually_le_nhds (by norm_num))
  have hlog4Upper : Real.log 4 ≤ (7 / 5 : ℝ) := by
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlog4]
    nlinarith [Real.log_two_lt_d9]
  have hlog4Nonneg : 0 ≤ Real.log 4 :=
    Real.log_nonneg (by norm_num)
  filter_upwards [eventually_ge_atTop 2,
    hLTop.eventually (eventually_ge_atTop (7 : ℝ)),
    hmajorSmall] with y hy2 hL7 hsmall
  have hLPos : 0 < L y := by linarith
  have hrecipRaw := fullReciprocalSum_le y hy2
  have hrecipDiv : fullReciprocalSum y / L y ≤ (1 / 5 : ℝ) := by
    calc
      fullReciprocalSum y / L y ≤
          (2 * Real.log 4 + 3 * Real.log 4 *
            (Real.log (L y) - Real.log (Real.log 2))) / L y := by
        exact div_le_div_of_nonneg_right hrecipRaw hLPos.le
      _ ≤ (1 / 5 : ℝ) := hsmall
  have hrecip :
      fullReciprocalSum y ≤ (1 / 5 : ℝ) * L y := by
    exact (div_le_iff₀ hLPos).mp hrecipDiv
  have hlogRaw := fullLogReciprocalSum_le y hy2
  have hlog :
      fullLogReciprocalSum y ≤ (8 / 5 : ℝ) * L y := by
    calc
      fullLogReciprocalSum y ≤ Real.log 4 * (1 + L y) := hlogRaw
      _ ≤ (8 / 5 : ℝ) * L y := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlog4Upper)
          (sub_nonneg.mpr hL7)]
  dsimp only [L] at hrecip hlog ⊢
  linarith

theorem eventually_roughHead_fullLogMoment_le_nine_fifths :
    ∀ᶠ y : ℕ in atTop,
      tangentSelbergFullLogMoment (roughHeadModulus y) ≤
        (9 / 5 : ℝ) * Real.log (y : ℝ) *
          tangentSelbergFullDensitySum (roughHeadModulus y) := by
  filter_upwards [eventually_fullPrimeMoment_le_nine_fifths_log]
      with y hprime
  have hEulerMoment := tangentSelbergFullLogMoment_le
    (roughHeadModulus_squarefree y)
  have hfactorNonneg :
      0 ≤ tangentSelbergFullDensitySum (roughHeadModulus y) := by
    rw [tangentSelbergFullDensitySum]
    exact Finset.sum_nonneg fun r hr ↦ by
      have hrPos := Nat.pos_of_mem_divisors hr
      have hphi : (0 : ℝ) < (r.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hrPos
      positivity
  calc
    tangentSelbergFullLogMoment (roughHeadModulus y) ≤
        tangentSelbergFullDensitySum (roughHeadModulus y) *
          (∑ p ∈ (roughHeadModulus y).primeFactors,
            Real.log (p : ℝ) / ((p : ℝ) - 1)) := hEulerMoment
    _ ≤ tangentSelbergFullDensitySum (roughHeadModulus y) *
        (fullLogReciprocalSum y + fullReciprocalSum y) := by
      exact mul_le_mul_of_nonneg_left
        (roughHead_primeFactor_logMoment_le_fullPrimeSums y) hfactorNonneg
    _ ≤ tangentSelbergFullDensitySum (roughHeadModulus y) *
        ((9 / 5 : ℝ) * Real.log (y : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hprime hfactorNonneg
    _ = (9 / 5 : ℝ) * Real.log (y : ℝ) *
        tangentSelbergFullDensitySum (roughHeadModulus y) := by ring

/-! ## Mertens lower bound for the full Euler product -/



theorem tangentSelbergMertensBase_ge_cutoff :
    fullReciprocalSumUniformCutoff ≤ tangentSelbergMertensBase :=
  le_max_left _ _

theorem tangentSelbergMertensBase_ge_two :
    2 ≤ tangentSelbergMertensBase :=
  le_max_right _ _





theorem fullReciprocalSum_ge_logLog_sub_tangentSelbergMertensLoss
    {y : ℕ} (hy : tangentSelbergMertensBase ≤ y) :
    Real.log (Real.log (y : ℝ)) - tangentSelbergMertensLoss ≤
      fullReciprocalSum y := by
  let A := tangentSelbergMertensBase
  have hquad := fullReciprocalSumUniform_bound A y
    tangentSelbergMertensBase_ge_cutoff hy
  have hlower :
      -(5 * fullReciprocalSumUniformConstant /
          Real.log (A : ℝ) ^ 3) ≤
        fullReciprocalSum y - fullReciprocalSum A -
          (Real.log (Real.log (y : ℝ)) -
            Real.log (Real.log (A : ℝ))) := by
    exact (neg_le_neg hquad).trans (neg_abs_le _)
  have hsumAbs :
      -|fullReciprocalSum A| ≤ fullReciprocalSum A :=
    neg_abs_le _
  have hlogAbs :
      -|Real.log (Real.log (A : ℝ))| ≤
        -Real.log (Real.log (A : ℝ)) := by
    exact neg_le_neg (le_abs_self _)
  dsimp only [A] at hlower hsumAbs hlogAbs ⊢
  unfold tangentSelbergMertensLoss
  linarith

private theorem exp_one_div_prime_le_one_add_inv_pred
    {p : ℕ} (hp : p.Prime) :
    Real.exp (1 / (p : ℝ)) ≤
      1 + 1 / ((p : ℝ) - 1) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpPred : (0 : ℝ) < (p : ℝ) - 1 := by
    have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hp.two_le
    linarith
  have hfactor : (0 : ℝ) < 1 + 1 / ((p : ℝ) - 1) := by
    positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hfactor
  have hid :
      1 - (1 + 1 / ((p : ℝ) - 1))⁻¹ = 1 / (p : ℝ) := by
    field_simp [hpR.ne', hpPred.ne']
    ring
  rw [hid] at hlog
  calc
    Real.exp (1 / (p : ℝ)) ≤
        Real.exp (Real.log (1 + 1 / ((p : ℝ) - 1))) :=
      Real.exp_le_exp.mpr hlog
    _ = 1 + 1 / ((p : ℝ) - 1) := Real.exp_log hfactor

theorem exp_fullReciprocalSum_le_roughHeadFullDensity (y : ℕ) :
    Real.exp (fullReciprocalSum y) ≤
      tangentSelbergFullDensitySum (roughHeadModulus y) := by
  rw [tangentSelbergFullDensitySum_eq_primeProduct
    (roughHeadModulus_squarefree y), roughHeadModulus_primeFactors,
    wholePaper_primesUpTo_eq_full_primesUpTo,
    fullReciprocalSum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hpPrime : p.Prime := by
      have hpData : p ≤ y ∧ p.Prime := by
        simpa [Erdos390.Full.PrimeSums.primesUpTo] using hp
      exact hpData.2
    exact exp_one_div_prime_le_one_add_inv_pred hpPrime

theorem roughHeadFullDensity_ge_exp_neg_loss_mul_log
    {y : ℕ} (hy : tangentSelbergMertensBase ≤ y) :
    Real.exp (-tangentSelbergMertensLoss) * Real.log (y : ℝ) ≤
      tangentSelbergFullDensitySum (roughHeadModulus y) := by
  have hy2 : 2 ≤ y := tangentSelbergMertensBase_ge_two.trans hy
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hMertens :=
    fullReciprocalSum_ge_logLog_sub_tangentSelbergMertensLoss hy
  calc
    Real.exp (-tangentSelbergMertensLoss) * Real.log (y : ℝ) =
        Real.exp (Real.log (Real.log (y : ℝ)) -
          tangentSelbergMertensLoss) := by
      rw [Real.exp_sub, Real.exp_log hlogPos]
      rw [Real.exp_neg]
      ring
    _ ≤ Real.exp (fullReciprocalSum y) :=
      Real.exp_le_exp.mpr hMertens
    _ ≤ tangentSelbergFullDensitySum (roughHeadModulus y) :=
      exp_fullReciprocalSum_le_roughHeadFullDensity y

/-! ## Retaining a fixed fraction below level `y^2` -/

theorem tangentSelbergFullDensitySum_le_density_add_logTail
    {P R : ℕ} (hP : Squarefree P) (hR : 1 < R) :
    tangentSelbergFullDensitySum P ≤
      tangentSelbergDensitySum P R +
        tangentSelbergFullLogMoment P / Real.log (R : ℝ) := by
  classical
  let w : ℕ → ℝ := fun r ↦ 1 / (r.totient : ℝ)
  let tail := P.divisors.filter (fun r ↦ ¬r ≤ R)
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  have hw (r : ℕ) (hr : r ∈ P.divisors) : 0 ≤ w r := by
    have hrPos := Nat.pos_of_mem_divisors hr
    have hphi : (0 : ℝ) < (r.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hrPos
    dsimp only [w]
    positivity
  have htailTerm (r : ℕ) (hr : r ∈ tail) :
      w r ≤ Real.log (r : ℝ) / Real.log (R : ℝ) * w r := by
    have hrData := Finset.mem_filter.mp hr
    have hRr : R < r := by omega
    have hRPos : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans hR)
    have hlogLe : Real.log (R : ℝ) ≤ Real.log (r : ℝ) :=
      Real.log_le_log hRPos (by exact_mod_cast hRr.le)
    have hone : (1 : ℝ) ≤
        Real.log (r : ℝ) / Real.log (R : ℝ) :=
      (le_div_iff₀ hlogR).2 (by simpa using hlogLe)
    have hwr := hw r hrData.1
    nlinarith
  have htail :
      (∑ r ∈ tail, w r) ≤
        tangentSelbergFullLogMoment P / Real.log (R : ℝ) := by
    calc
      (∑ r ∈ tail, w r) ≤
          ∑ r ∈ tail,
            Real.log (r : ℝ) / Real.log (R : ℝ) * w r := by
        exact Finset.sum_le_sum fun r hr ↦ htailTerm r hr
      _ = (∑ r ∈ tail,
          Real.log (r : ℝ) / (r.totient : ℝ)) /
            Real.log (R : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r _hr
        dsimp only [w]
        ring
      _ ≤ tangentSelbergFullLogMoment P / Real.log (R : ℝ) := by
        apply div_le_div_of_nonneg_right _ hlogR.le
        rw [tangentSelbergFullLogMoment]
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro r hr _hrTail
        have hrPos := Nat.pos_of_mem_divisors hr
        have hlogNonneg : 0 ≤ Real.log (r : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hrPos)
        have hphi : (0 : ℝ) < (r.totient : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr hrPos
        positivity
  have hsplit :
      tangentSelbergFullDensitySum P =
        (∑ r ∈ tangentSelbergLambdaSupport P R, w r) +
          ∑ r ∈ tail, w r := by
    rw [tangentSelbergFullDensitySum, tangentSelbergLambdaSupport]
    dsimp only [tail]
    simpa only [w] using
      (Finset.sum_filter_add_sum_filter_not P.divisors
        (fun r ↦ r ≤ R) w).symm
  rw [hsplit, tangentSelbergDensitySum_eq_reciprocalTotient hP]
  dsimp only [w]
  exact add_le_add_right htail _

theorem eventually_roughHead_density_ge_one_tenth_fullDensity :
    ∀ᶠ y : ℕ in atTop,
      tangentSelbergFullDensitySum (roughHeadModulus y) / 10 ≤
        tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_roughHead_fullLogMoment_le_nine_fifths]
      with y hy2 hmoment
  let D := tangentSelbergFullDensitySum (roughHeadModulus y)
  let G := tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2)
  let M := tangentSelbergFullLogMoment (roughHeadModulus y)
  have hyLog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hySq : 1 < y ^ 2 := by nlinarith
  have hlogSq : Real.log ((y ^ 2 : ℕ) : ℝ) =
      2 * Real.log (y : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have htruncate := tangentSelbergFullDensitySum_le_density_add_logTail
    (roughHeadModulus_squarefree y) hySq
  have htail :
      M / Real.log ((y ^ 2 : ℕ) : ℝ) ≤ (9 / 10 : ℝ) * D := by
    rw [hlogSq]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log (y : ℝ))).2
    dsimp only [M, D]
    nlinarith [hmoment]
  dsimp only [D, G, M] at htruncate htail ⊢
  linarith

/-! ## A universal `exp 4` coefficient-mean bound -/

theorem tangentSigmaTotientRatio_le_fourConvolution_of_squarefree
    {r : ℕ} (hr : Squarefree r) :
    ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
        (r.totient : ℝ) ≤
      (tangentSquarefreeFourOverPrimeArithmeticFunction *
        (ζ : ArithmeticFunction ℝ)) r := by
  let A := tangentSigmaTotientRatioArithmeticFunction
  let H := tangentSquarefreeFourOverPrimeArithmeticFunction
  have hAprod :=
    tangentSigmaTotientRatioArithmeticFunction_isMultiplicative.prod_primeFactors hr
  have hHprod :=
    tangentSquarefreeFourOverPrimeArithmeticFunction_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
      hr
  have hlocal : ∀ p ∈ r.primeFactors,
      A p ≤ 1 + H p := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hpPred : (0 : ℝ) < (p : ℝ) - 1 := by
      have hpOneR : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast hpPrime.one_lt
      linarith
    have hsigma : ArithmeticFunction.sigma 1 p = p + 1 := by
      rw [← pow_one p,
        ArithmeticFunction.sigma_apply_prime_pow hpPrime]
      simp
    rw [show A p = ((ArithmeticFunction.sigma 1 p : ℕ) : ℝ) /
          (p.totient : ℝ) by
        exact tangentSigmaTotientRatioArithmeticFunction_apply_of_pos
          hpPrime.pos,
      hsigma, Nat.totient_prime hpPrime]
    rw [show H p = 4 / (p : ℝ) by
      exact tangentSquarefreeFourOverPrimeArithmeticFunction_apply_prime
        hpPrime]
    rw [Nat.cast_add, Nat.cast_sub hpPrime.one_le, Nat.cast_one]
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hpPrime.two_le
    have hfrac :
        2 / ((p : ℝ) - 1) ≤ 4 / (p : ℝ) := by
      apply (div_le_div_iff₀ hpPred hpR).2
      nlinarith
    calc
      ((p : ℝ) + 1) / ((p : ℝ) - 1) =
          1 + 2 / ((p : ℝ) - 1) := by
        field_simp [hpPred.ne']
        ring
      _ ≤ 1 + 4 / (p : ℝ) := add_le_add_right hfrac 1
  have hAnonneg : ∀ p ∈ r.primeFactors, 0 ≤ A p := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    rw [show A p = ((ArithmeticFunction.sigma 1 p : ℕ) : ℝ) /
          (p.totient : ℝ) by
      exact tangentSigmaTotientRatioArithmeticFunction_apply_of_pos
        hpPrime.pos]
    positivity
  calc
    ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ) = A r := by
      symm
      exact tangentSigmaTotientRatioArithmeticFunction_apply_of_pos
        (Nat.pos_of_ne_zero hr.ne_zero)
    _ = ∏ p ∈ r.primeFactors, A p := hAprod.symm
    _ ≤ ∏ p ∈ r.primeFactors, (1 + H p) := by
      exact Finset.prod_le_prod hAnonneg hlocal
    _ = ∑ d ∈ r.divisors, H d := hHprod
    _ = (H * (ζ : ArithmeticFunction ℝ)) r := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = (tangentSquarefreeFourOverPrimeArithmeticFunction *
        (ζ : ArithmeticFunction ℝ)) r := rfl

theorem tangent_fourOverPrime_convolution_nonneg (r : ℕ) :
    0 ≤ (tangentSquarefreeFourOverPrimeArithmeticFunction *
      (ζ : ArithmeticFunction ℝ)) r := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  exact Finset.sum_nonneg fun d _hd ↦
    tangentSquarefreeFourOverPrimeArithmeticFunction_nonneg d

private theorem roughHead_prime_reciprocalSquareSum_le_one
    {R : ℕ} (hR : 1 ≤ R) :
    (∑ p ∈ primesUpTo R, 1 / (p : ℝ) ^ 2) ≤ 1 := by
  have hsubset : primesUpTo R ⊆ Finset.Ioc 1 R := by
    intro p hp
    have hpData := mem_primesUpTo.mp hp
    exact Finset.mem_Ioc.mpr ⟨hpData.1.one_lt, hpData.2⟩
  calc
    (∑ p ∈ primesUpTo R, 1 / (p : ℝ) ^ 2) ≤
        ∑ n ∈ Finset.Ioc 1 R, 1 / (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n hn _hnPrime
      positivity
    _ ≤ (1 : ℝ)⁻¹ - (R : ℝ)⁻¹ := by
      simpa only [one_div, Nat.cast_one] using
        (sum_Ioc_inv_sq_le_sub (α := ℝ)
          (k := 1) (n := R) one_ne_zero hR)
    _ ≤ 1 := by
      norm_num

theorem roughHead_fourOverSquareEulerProduct_le_exp_four
    {R : ℕ} (hR : 1 ≤ R) :
    (∏ p ∈ primesUpTo R, (1 + 4 / (p : ℝ) ^ 2)) ≤
      Real.exp 4 := by
  calc
    (∏ p ∈ primesUpTo R, (1 + 4 / (p : ℝ) ^ 2)) ≤
        ∏ p ∈ primesUpTo R, Real.exp (4 / (p : ℝ) ^ 2) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime := (mem_primesUpTo.mp hp).1
        have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
        positivity
      · intro p hp
        simpa only [add_comm] using
          Real.add_one_le_exp (4 / (p : ℝ) ^ 2)
    _ = Real.exp (∑ p ∈ primesUpTo R, 4 / (p : ℝ) ^ 2) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp 4 := by
      apply Real.exp_le_exp.mpr
      calc
        (∑ p ∈ primesUpTo R, 4 / (p : ℝ) ^ 2) =
            4 * ∑ p ∈ primesUpTo R, 1 / (p : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        _ ≤ 4 * 1 := by
          exact mul_le_mul_of_nonneg_left
            (roughHead_prime_reciprocalSquareSum_le_one hR) (by norm_num)
        _ = 4 := by norm_num

private theorem squarefree_le_dvd_roughHeadModulus
    {q R : ℕ} (hqPos : 0 < q) (hqR : q ≤ R) (hqsq : Squarefree q) :
    q ∣ roughHeadModulus R := by
  have hsubset : q.primeFactors ⊆ primesUpTo R := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpDvd := Nat.dvd_of_mem_primeFactors hp
    exact mem_primesUpTo.mpr
      ⟨hpPrime, (Nat.le_of_dvd hqPos hpDvd).trans hqR⟩
  rw [← Nat.prod_primeFactors_of_squarefree hqsq, roughHeadModulus]
  exact Finset.prod_dvd_prod_of_subset q.primeFactors (primesUpTo R) id
    hsubset

theorem sum_fourOverSquare_le_exp_four
    {R : ℕ} (hR : 1 ≤ R) :
    (∑ q ∈ Finset.Ioc 0 R,
        tangentSquarefreeFourOverSquareArithmeticFunction q) ≤
      Real.exp 4 := by
  let K := tangentSquarefreeFourOverSquareArithmeticFunction
  have hfilter :
      (∑ q ∈ Finset.Ioc 0 R, K q) =
        ∑ q ∈ (Finset.Ioc 0 R).filter Squarefree, K q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hsq : Squarefree q
    · simp [hsq]
    · have hzero : K q = 0 := by
        dsimp only [K, tangentSquarefreeFourOverSquareArithmeticFunction]
        rw [ArithmeticFunction.pmul_apply,
          tangentSquarefreeFourOverPrimeArithmeticFunction_eq_zero_of_not_squarefree
            hsq,
          zero_mul]
      simp [hsq, hzero]
  have hsubset : (Finset.Ioc 0 R).filter Squarefree ⊆
      (roughHeadModulus R).divisors := by
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    have hqIoc := Finset.mem_Ioc.mp hqData.1
    exact Nat.mem_divisors.mpr
      ⟨squarefree_le_dvd_roughHeadModulus hqIoc.1 hqIoc.2 hqData.2,
        (roughHeadModulus_pos R).ne'⟩
  have hEuler :=
    tangentSquarefreeFourOverSquareArithmeticFunction_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (roughHeadModulus_squarefree R)
  calc
    (∑ q ∈ Finset.Ioc 0 R, K q) =
        ∑ q ∈ (Finset.Ioc 0 R).filter Squarefree, K q := hfilter
    _ ≤ ∑ q ∈ (roughHeadModulus R).divisors, K q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro q hq _hqSmall
      exact tangentSquarefreeFourOverSquareArithmeticFunction_nonneg q
    _ = ∏ p ∈ (roughHeadModulus R).primeFactors,
        (1 + K p) := hEuler.symm
    _ = ∏ p ∈ primesUpTo R, (1 + 4 / (p : ℝ) ^ 2) := by
      rw [roughHeadModulus_primeFactors]
      apply Finset.prod_congr rfl
      intro p hp
      rw [show K p = 4 / (p : ℝ) ^ 2 by
        exact tangentSquarefreeFourOverSquareArithmeticFunction_apply_prime
          (mem_primesUpTo.mp hp).1]
    _ ≤ Real.exp 4 := roughHead_fourOverSquareEulerProduct_le_exp_four hR

theorem tangentSelbergSigmaTotientMean_le
    {P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    (∑ r ∈ tangentSelbergLambdaSupport P R,
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ)) ≤
      Real.exp 4 * (R : ℝ) := by
  let H := tangentSquarefreeFourOverPrimeArithmeticFunction
  let K := tangentSquarefreeFourOverSquareArithmeticFunction
  let C := H * (ζ : ArithmeticFunction ℝ)
  have hsupport : tangentSelbergLambdaSupport P R ⊆ Finset.Ioc 0 R := by
    intro r hr
    have hrData := mem_tangentSelbergLambdaSupport.mp hr
    exact Finset.mem_Ioc.mpr
      ⟨tangentSelbergLambdaSupport_pos hr, hrData.2⟩
  have hpoint : ∀ r ∈ tangentSelbergLambdaSupport P R,
      ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ) ≤ C r := by
    intro r hr
    have hrData := mem_tangentSelbergLambdaSupport.mp hr
    have hrsq := hP.squarefree_of_dvd hrData.1.1
    simpa only [C] using
      tangentSigmaTotientRatio_le_fourConvolution_of_squarefree hrsq
  have hconv :
      (∑ r ∈ Finset.Ioc 0 R, C r) =
        ∑ q ∈ Finset.Ioc 0 R, H q * ((R / q : ℕ) : ℝ) := by
    simpa only [C] using
      ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum H R
  have hswitch :
      (∑ q ∈ Finset.Ioc 0 R, H q * ((R / q : ℕ) : ℝ)) ≤
        (R : ℝ) * ∑ q ∈ Finset.Ioc 0 R, K q := by
    calc
      (∑ q ∈ Finset.Ioc 0 R,
          H q * ((R / q : ℕ) : ℝ)) ≤
          ∑ q ∈ Finset.Ioc 0 R,
            H q * ((R : ℝ) / (q : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left Nat.cast_div_le
        exact tangentSquarefreeFourOverPrimeArithmeticFunction_nonneg q
      _ = (R : ℝ) * ∑ q ∈ Finset.Ioc 0 R, K q := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        have hqPos := (Finset.mem_Ioc.mp hq).1
        rw [show K q = H q * (1 / (q : ℝ)) by
          dsimp only [K, tangentSquarefreeFourOverSquareArithmeticFunction]
          rw [ArithmeticFunction.pmul_apply,
            tangentReciprocalArithmeticFunction_apply_of_pos hqPos]]
        ring
  calc
    (∑ r ∈ tangentSelbergLambdaSupport P R,
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ)) ≤
        ∑ r ∈ tangentSelbergLambdaSupport P R, C r := by
      exact Finset.sum_le_sum hpoint
    _ ≤ ∑ r ∈ Finset.Ioc 0 R, C r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsupport
      intro r hr _hrS
      exact tangent_fourOverPrime_convolution_nonneg r
    _ = ∑ q ∈ Finset.Ioc 0 R,
        H q * ((R / q : ℕ) : ℝ) := hconv
    _ ≤ (R : ℝ) * ∑ q ∈ Finset.Ioc 0 R, K q := hswitch
    _ ≤ (R : ℝ) * Real.exp 4 := by
      exact mul_le_mul_of_nonneg_left (sum_fourOverSquare_le_exp_four hR)
        (Nat.cast_nonneg R)
    _ = Real.exp 4 * (R : ℝ) := by ring

/-! ## The canonical Lambda norm -/

theorem tangentSelbergCanonicalLambda_abs_le
    {P R d : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (hd : d ∈ tangentSelbergLambdaSupport P R) :
    |tangentSelbergCanonicalLambda P R d| ≤
      (d : ℝ) / tangentSelbergDensitySum P R *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          if d ∣ r then 1 / (r.totient : ℝ) else 0 := by
  let S := tangentSelbergLambdaSupport P R
  have hPPos : 0 < P := Nat.pos_of_ne_zero hP.ne_zero
  have hGPos : 0 < tangentSelbergDensitySum P R :=
    tangentSelbergDensitySum_pos hPPos hR
  have hdPos := tangentSelbergLambdaSupport_pos hd
  have hfactor : 0 ≤ (d : ℝ) / tangentSelbergDensitySum P R := by
    positivity
  rw [tangentSelbergCanonicalLambda, if_pos hd, abs_mul,
    abs_of_nonneg hfactor]
  apply mul_le_mul_of_nonneg_left _ hfactor
  calc
    |∑ r ∈ S,
        if d ∣ r then
          (ArithmeticFunction.moebius (r / d) : ℝ) *
              (ArithmeticFunction.moebius r : ℝ) /
            (r.totient : ℝ)
        else 0| ≤
        ∑ r ∈ S,
          |if d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) *
                (ArithmeticFunction.moebius r : ℝ) /
              (r.totient : ℝ)
          else 0| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r ∈ S,
        if d ∣ r then 1 / (r.totient : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hdr : d ∣ r
      · have hrData := mem_tangentSelbergLambdaSupport.mp hr
        have hrsq : Squarefree r := hP.squarefree_of_dvd hrData.1.1
        have hquotDvd : r / d ∣ r := by
          refine ⟨d, ?_⟩
          exact (Nat.div_mul_cancel hdr).symm
        have hquotSq : Squarefree (r / d) :=
          hrsq.squarefree_of_dvd hquotDvd
        have hmuQuotZ :=
          ArithmeticFunction.abs_moebius_eq_one_of_squarefree hquotSq
        have hmuRZ :=
          ArithmeticFunction.abs_moebius_eq_one_of_squarefree hrsq
        have hmuQuot :
            |(ArithmeticFunction.moebius (r / d) : ℝ)| = 1 := by
          exact_mod_cast hmuQuotZ
        have hmuR : |(ArithmeticFunction.moebius r : ℝ)| = 1 := by
          exact_mod_cast hmuRZ
        have hrPos := tangentSelbergLambdaSupport_pos hr
        have hphi : (0 : ℝ) < (r.totient : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr hrPos
        simp only [hdr, if_true, abs_div, abs_mul, hmuQuot, hmuR,
          one_mul, abs_of_pos hphi]
      · simp [hdr]

theorem tangentSelbergCanonicalLambda_l1_le_sigmaTotientMean
    {P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        |tangentSelbergCanonicalLambda P R d|) ≤
      (1 / tangentSelbergDensitySum P R) *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
            (r.totient : ℝ) := by
  classical
  let S := tangentSelbergLambdaSupport P R
  let G := tangentSelbergDensitySum P R
  have hcoeff : ∀ d ∈ S,
      |tangentSelbergCanonicalLambda P R d| ≤
        (d : ℝ) / G *
          ∑ r ∈ S, if d ∣ r then 1 / (r.totient : ℝ) else 0 := by
    intro d hd
    simpa only [S, G] using
      tangentSelbergCanonicalLambda_abs_le hP hR hd
  have hdivisorSum : ∀ r ∈ S,
      (∑ d ∈ S, if d ∣ r then (d : ℝ) else 0) =
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) := by
    intro r hr
    have hrData := mem_tangentSelbergLambdaSupport.mp hr
    have hrPos := tangentSelbergLambdaSupport_pos hr
    have hfilter : S.filter (fun d ↦ d ∣ r) = r.divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨_hdS, hdr⟩
        exact ⟨hdr, hrPos.ne'⟩
      · rintro ⟨hdr, _hr0⟩
        have hdLeR : d ≤ R :=
          (Nat.le_of_dvd hrPos hdr).trans hrData.2
        exact ⟨mem_tangentSelbergLambdaSupport.mpr
          ⟨⟨hdr.trans hrData.1.1, hrData.1.2⟩, hdLeR⟩, hdr⟩
    rw [← Finset.sum_filter, hfilter,
      ← Nat.cast_sum, ← ArithmeticFunction.sigma_one_apply]
  calc
    (∑ d ∈ S, |tangentSelbergCanonicalLambda P R d|) ≤
        ∑ d ∈ S, (d : ℝ) / G *
          ∑ r ∈ S,
            if d ∣ r then 1 / (r.totient : ℝ) else 0 := by
      exact Finset.sum_le_sum hcoeff
    _ = ∑ r ∈ S, (1 / G) *
        ∑ d ∈ S,
          if d ∣ r then (d : ℝ) / (r.totient : ℝ) else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdr : d ∣ r
      · simp only [hdr, if_true]
        ring
      · simp [hdr]
    _ = ∑ r ∈ S, (1 / G) *
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hinner :
        (∑ d ∈ S,
            if d ∣ r then (d : ℝ) / (r.totient : ℝ) else 0) =
            (∑ d ∈ S, if d ∣ r then (d : ℝ) else 0) /
              (r.totient : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdr : d ∣ r <;> simp [hdr]
      rw [hinner, hdivisorSum r hr]
      ring
    _ = (1 / G) * ∑ r ∈ S,
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = (1 / tangentSelbergDensitySum P R) *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
            (r.totient : ℝ) := rfl

theorem tangentSelbergCanonicalLambda_l1_le_exp_four_mul_level_div_density
    {P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        |tangentSelbergCanonicalLambda P R d|) ≤
      Real.exp 4 * (R : ℝ) /
        tangentSelbergDensitySum P R := by
  have hPPos : 0 < P := Nat.pos_of_ne_zero hP.ne_zero
  have hGPos := tangentSelbergDensitySum_pos hPPos hR
  have hmean := tangentSelbergSigmaTotientMean_le hP hR
  calc
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        |tangentSelbergCanonicalLambda P R d|) ≤
        (1 / tangentSelbergDensitySum P R) *
          ∑ r ∈ tangentSelbergLambdaSupport P R,
            ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
              (r.totient : ℝ) :=
      tangentSelbergCanonicalLambda_l1_le_sigmaTotientMean hP hR
    _ ≤ (1 / tangentSelbergDensitySum P R) *
        (Real.exp 4 * (R : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = Real.exp 4 * (R : ℝ) /
        tangentSelbergDensitySum P R := by ring

/-! ## Fixed eventual constants and the closed interval theorem -/





theorem tangentSelbergCanonicalMainConstant_pos :
    0 < tangentSelbergCanonicalMainConstant := by
  unfold tangentSelbergCanonicalMainConstant
  positivity



/-- The two coefficient estimates needed by the canonical paper-shape
theorem, with fixed named constants and one common eventual cutoff. -/
theorem eventually_tangentSelbergCanonical_coefficientBounds :
    ∀ᶠ y : ℕ in atTop,
      1 / tangentSelbergDensitySum
          (roughHeadModulus y) (y ^ 2) ≤
          tangentSelbergCanonicalMainConstant /
            Real.log (y : ℝ) ∧
      (∑ d ∈ tangentSelbergLambdaSupport
          (roughHeadModulus y) (y ^ 2),
          |tangentSelbergCanonicalLambda
            (roughHeadModulus y) (y ^ 2) d|) ≤
          tangentSelbergCanonicalLambdaConstant * (y : ℝ) ^ 2 /
            Real.log (y : ℝ) := by
  filter_upwards [eventually_ge_atTop tangentSelbergMertensBase,
    eventually_roughHead_density_ge_one_tenth_fullDensity]
      with y hyBase hfraction
  have hy2 : 2 ≤ y := tangentSelbergMertensBase_ge_two.trans hyBase
  have hyOne : 1 ≤ y := by omega
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hGPos :
      0 < tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) :=
    tangentSelbergDensitySum_pos (roughHeadModulus_pos y)
      (one_le_pow₀ hyOne)
  have hfull := roughHeadFullDensity_ge_exp_neg_loss_mul_log hyBase
  have hlower :
      Real.exp (-tangentSelbergMertensLoss) * Real.log (y : ℝ) / 10 ≤
        tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) := by
    calc
      Real.exp (-tangentSelbergMertensLoss) * Real.log (y : ℝ) / 10 ≤
          tangentSelbergFullDensitySum (roughHeadModulus y) / 10 := by
        exact div_le_div_of_nonneg_right hfull (by norm_num)
      _ ≤ tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) :=
        hfraction
  have hcross :
      Real.log (y : ℝ) ≤
        tangentSelbergCanonicalMainConstant *
          tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) := by
    calc
      Real.log (y : ℝ) =
          tangentSelbergCanonicalMainConstant *
            (Real.exp (-tangentSelbergMertensLoss) *
              Real.log (y : ℝ) / 10) := by
        unfold tangentSelbergCanonicalMainConstant
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
      _ ≤ tangentSelbergCanonicalMainConstant *
          tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) := by
        exact mul_le_mul_of_nonneg_left hlower
          tangentSelbergCanonicalMainConstant_pos.le
  have hdensity :
      1 / tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) ≤
        tangentSelbergCanonicalMainConstant / Real.log (y : ℝ) := by
    apply (div_le_div_iff₀ hGPos hlogPos).2
    simpa only [one_mul] using hcross
  have hnormRaw :=
    tangentSelbergCanonicalLambda_l1_le_exp_four_mul_level_div_density
      (P := roughHeadModulus y) (R := y ^ 2)
      (roughHeadModulus_squarefree y) (one_le_pow₀ hyOne)
  have hfactorNonneg :
      0 ≤ Real.exp 4 * (y : ℝ) ^ 2 := by positivity
  have hnorm :
      (∑ d ∈ tangentSelbergLambdaSupport
          (roughHeadModulus y) (y ^ 2),
          |tangentSelbergCanonicalLambda
            (roughHeadModulus y) (y ^ 2) d|) ≤
        tangentSelbergCanonicalLambdaConstant * (y : ℝ) ^ 2 /
          Real.log (y : ℝ) := by
    calc
      (∑ d ∈ tangentSelbergLambdaSupport
          (roughHeadModulus y) (y ^ 2),
          |tangentSelbergCanonicalLambda
            (roughHeadModulus y) (y ^ 2) d|) ≤
          Real.exp 4 * ((y ^ 2 : ℕ) : ℝ) /
            tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) :=
        hnormRaw
      _ = (Real.exp 4 * (y : ℝ) ^ 2) *
          (1 / tangentSelbergDensitySum
            (roughHeadModulus y) (y ^ 2)) := by
        rw [Nat.cast_pow]
        ring
      _ ≤ (Real.exp 4 * (y : ℝ) ^ 2) *
          (tangentSelbergCanonicalMainConstant /
            Real.log (y : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hdensity hfactorNonneg
      _ = tangentSelbergCanonicalLambdaConstant * (y : ℝ) ^ 2 /
          Real.log (y : ℝ) := by
        unfold tangentSelbergCanonicalLambdaConstant
        ring
  exact ⟨hdensity, hnorm⟩







/-- Assumption-free eventual paper-shape interval estimate for the actual
rough-head modulus and the actual canonical finite Selberg weights. -/
theorem eventually_reducedResidueIoc_card_le_canonicalLambdaSquare_roughHead :
    ∀ᶠ y : ℕ in atTop, ∀ lo hi : ℕ,
      ((reducedResidueIoc (roughHeadModulus y) lo hi).card : ℝ) ≤
        ((hi - lo : ℕ) : ℝ) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (y : ℝ)) +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
            Real.log (y : ℝ) ^ 2 := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_tangentSelbergCanonical_coefficientBounds]
      with y hy2 hbounds
  intro lo hi
  exact reducedResidueIoc_card_le_canonicalLambdaSquare_paperShape
    (roughHeadModulus_squarefree y) (by omega) hbounds.1 hbounds.2

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCanonicalCleanListLower -/
section


/-!
# Canonical eventual lower bounds for tangent clean lists

This file composes the three previously separate parts of the tangent-list
cardinality argument.

* `FixedModulusReducedResidueCount` gives a lower bound for the literal
  candidate interval

  `(n / v, tangentBroadUpper n K h / u]`

  with modulus `roughHeadModulus W`.  The endpoint loss is the literal
  modulus, not an absorbed constant.
* `TangentExceptionalCanonicalBounds` is applied to every rough-label
  interval indexed by a smooth factor `b`.  The resulting exceptional upper
  bound is assumption-free eventually in `y` and then in `yNat n`.
* `TangentCleanListCardinalityBridge` subtracts that exceptional bound and
  the declared deterministic deletion budget from the candidate lower bound.

The accumulated canonical remainder is displayed as

`(X0 / u) * C_lambda^2 * y^4 / log(y)^2`.

After normalization by the candidate scale `n/u`, it is bounded by the
explicit quantity

`C_lambda^2 * (X0 * y^4 / n) / log(y)^2`.

Thus the power-saving input is genuinely `X0*y^4/n`; the logarithmic square
does not conceal the required scale.  The final paper wrappers leave only an
explicit comparison between the candidate floor and the effective lower-card
ceiling plus the exceptional and deterministic losses.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal candidate lower bound -/





/-- Fixed-modulus periodicity supplies the candidate lower bound on the
literal common-multiplier interval. -/
theorem tangentRoughHeadCandidateLower_le_card
    {W n K h u v : ℕ}
    (hinterval : n / v ≤ tangentBroadUpper n K h / u) :
    tangentRoughHeadCandidateLower W n K h u v ≤
      (tangentHeadCoprimeCandidates
        n K h (roughHeadModulus W) u v).card := by
  have herror := reducedResidueIoc_card_error_le_modulus
    (roughHeadModulus_pos W) hinterval
  have herror' :
      abs (((reducedResidueIoc (roughHeadModulus W) (n / v)
          (tangentBroadUpper n K h / u)).card : ℝ) -
        roughHeadDensity W *
          (((tangentBroadUpper n K h / u - n / v : ℕ) : ℝ))) ≤
        (roughHeadModulus W : ℝ) := by
    simpa only [fixedModulusReducedResidueDensity, roughHeadDensity]
      using herror
  have hmainLower :
      tangentRoughHeadCandidateMain W n K h u v ≤
        ((reducedResidueIoc (roughHeadModulus W) (n / v)
          (tangentBroadUpper n K h / u)).card : ℝ) := by
    unfold tangentRoughHeadCandidateMain
    linarith [(abs_le.mp herror').1]
  have hnonneg :
      (0 : ℝ) ≤
        ((reducedResidueIoc (roughHeadModulus W) (n / v)
          (tangentBroadUpper n K h / u)).card : ℝ) :=
    Nat.cast_nonneg _
  have hmax :
      max 0 (tangentRoughHeadCandidateMain W n K h u v) ≤
        ((reducedResidueIoc (roughHeadModulus W) (n / v)
          (tangentBroadUpper n K h / u)).card : ℝ) :=
    max_le hnonneg hmainLower
  have hfloor :
      (tangentRoughHeadCandidateLower W n K h u v : ℝ) ≤
        max 0 (tangentRoughHeadCandidateMain W n K h u v) := by
    unfold tangentRoughHeadCandidateLower
    exact Nat.floor_le (le_max_left _ _)
  rw [tangentHeadCoprimeCandidates_eq_reducedResidueIoc]
  exact_mod_cast (hfloor.trans hmax)

/-! ## Assumption-free canonical exceptional upper bound -/









/-- Applying the assumption-free canonical interval theorem to every smooth
factor gives the complete exceptional-row estimate, uniformly in all finite
interval parameters. -/
theorem eventually_tangentExceptionalMultipliers_card_cast_le_canonicalUpper :
    ∀ᶠ y : ℕ in atTop, ∀ n K h X0 u v : ℕ,
      0 < u → 0 < v →
      ((tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
        tangentCanonicalExceptionalUpper n K h X0 y u v := by
  filter_upwards
    [eventually_reducedResidueIoc_card_le_canonicalLambdaSquare_roughHead]
      with y hy
  intro n K h X0 u v hu hv
  let mainTerm :=
    tangentSelbergCanonicalMainConstant / Real.log (y : ℝ)
  let remainderTerm :=
    tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
      Real.log (y : ℝ) ^ 2
  have hremainderNonneg : 0 ≤ remainderTerm := by
    dsimp only [remainderTerm]
    positivity
  have hcount := card_tangentExceptionalMultipliers_le_sieveSum
    (n := n) (K := K) (h := h) (X0 := X0) (y := y)
      (u := u) (v := v) hu hv
  have hindexCard :
      ((tangentExceptionalSmoothIndices X0 u).card : ℝ) ≤
        ((X0 / u : ℕ) : ℝ) := by
    exact_mod_cast card_tangentExceptionalSmoothIndices_le_div hu
  calc
    ((tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
        ((∑ b ∈ tangentExceptionalSmoothIndices X0 u,
          (tangentExceptionalRoughCandidates
            n K h y u v b).card : ℕ) : ℝ) := by
      exact_mod_cast hcount
    _ = ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        ((tangentExceptionalRoughCandidates
          n K h y u v b).card : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (((tangentBroadUpper n K h / (u * b) -
            n / (v * b) : ℕ) : ℝ) * mainTerm + remainderTerm) := by
      apply Finset.sum_le_sum
      intro b _hb
      simpa only [tangentExceptionalRoughCandidates, mainTerm,
        remainderTerm] using
          hy (n / (v * b)) (tangentBroadUpper n K h / (u * b))
    _ = tangentCanonicalExceptionalLengthSum n K h X0 u v * mainTerm +
        ((tangentExceptionalSmoothIndices X0 u).card : ℝ) *
          remainderTerm := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [Finset.sum_const, nsmul_eq_mul,
        tangentCanonicalExceptionalLengthSum]
    _ ≤ tangentCanonicalExceptionalLengthSum n K h X0 u v * mainTerm +
        ((X0 / u : ℕ) : ℝ) * remainderTerm := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right hindexCard hremainderNonneg) _
    _ = tangentCanonicalExceptionalUpper n K h X0 y u v := by
      simp only [tangentCanonicalExceptionalUpper,
        tangentCanonicalExceptionalRemainder, mainTerm, remainderTerm]

/-- Natural-cardinality form of the preceding eventual estimate. -/
theorem eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper :
    ∀ᶠ y : ℕ in atTop, ∀ n K h X0 u v : ℕ,
      0 < u → 0 < v →
      (tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card ≤
        tangentCanonicalExceptionalNatUpper n K h X0 y u v := by
  filter_upwards
    [eventually_tangentExceptionalMultipliers_card_cast_le_canonicalUpper]
      with y hy
  intro n K h X0 u v hu hv
  have hreal := hy n K h X0 u v hu hv
  have hceil := hreal.trans
    (Nat.le_ceil (tangentCanonicalExceptionalUpper n K h X0 y u v))
  unfold tangentCanonicalExceptionalNatUpper
  exact_mod_cast hceil



/-! ## Effective lower cards and eventual bridge theorems -/



/-- Multiplying the effective ceiling by its defining endpoint label
recovers at least the requested real density scale. -/
theorem tangentEffectiveLowerCard_scale
    {density : ℝ} {n smallerLabel : ℕ}
    (hsmaller : 0 < smallerLabel) :
    density * n ≤
      (tangentEffectiveLowerCard density n smallerLabel : ℝ) *
        smallerLabel := by
  unfold tangentEffectiveLowerCard
  apply (div_le_iff₀ (by exact_mod_cast hsmaller)).mp
  exact Nat.le_ceil (density * (n : ℝ) / smallerLabel)

private theorem tangentCanonicalClean_yNat_tendsto_atTop :
    Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

/-- Assumption-free exceptional-cardinality estimate on the paper's moving
cutoff `yNat n`. -/
theorem eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper_yNat :
    ∀ᶠ n : ℕ in atTop, ∀ K h X0 u v : ℕ,
      0 < u → 0 < v →
      (tangentExceptionalMultipliers n X0 (yNat n)
        (tangentCommonMultiplierInterval n K h u v)).card ≤
        tangentCanonicalExceptionalNatUpper
          n K h X0 (yNat n) u v := by
  have hevent := tangentCanonicalClean_yNat_tendsto_atTop.eventually
    eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper
  filter_upwards [hevent] with n hn
  intro K h X0 u v hu hv
  exact hn n K h X0 u v hu hv



namespace BankPaperRealization

/-- Sharp-paper-facing eventual theorem.  The actual canonical exceptional
estimate and fixed-head candidate count are invoked internally; only the
displayed interval geometry and the final density-versus-loss comparison
remain. -/
theorem eventually_tangentPaperCleanCommonMultiplierList_card_lower_canonical :
    ∀ᶠ n : ℕ in atTop,
      ∀ (c : ℝ) (depth M W K h X0 u v : ℕ)
        (left right : ℕ → ℕ) (changed : Finset ℕ),
      ∀ (R : BankPaperRealization n M)
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed)
        (fixedExceptional : Finset ℕ) (density : ℝ),
      fixedExceptional ⊆ Finset.Ioc (2 * n) M →
      2 ≤ W → 2 * depth + 1 ≤ W →
      W < v → v ≤ u → u ≤ yNat n →
      yNat n < centralAnchorCutoff depth n →
      u.Prime → v.Prime → 0 < density →
      n / v ≤ tangentBroadUpper n K h / u →
      tangentEffectiveLowerCard density n v +
          tangentCanonicalExceptionalNatUpper
            n K h X0 (yNat n) u v +
          4 + 4 * bankPaperSharpMarkerBudget n ≤
        tangentRoughHeadCandidateLower W n K h u v →
      0 < tangentEffectiveLowerCard density n v ∧
        tangentEffectiveLowerCard density n v ≤
          (tangentCleanCommonMultiplierList n K h
            (roughHeadModulus W) X0 (yNat n) u v
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional)).card ∧
        density * n ≤
          (tangentEffectiveLowerCard density n v : ℝ) * u ∧
        density * n ≤
          (tangentEffectiveLowerCard density n v : ℝ) * v := by
  filter_upwards
    [eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper_yNat,
      eventually_gt_atTop 0]
      with n hexceptional hn
  intro c depth M W K h X0 u v left right changed R certificate
    fixedExceptional density hfixedTail hTwoW hPrefix hWv hvu huy
    hyCutoff huPrime hvPrime hdensity hinterval harithmetic
  have hcandidate := tangentRoughHeadCandidateLower_le_card
    (W := W) (n := n) (K := K) (h := h) (u := u) (v := v) hinterval
  have hlower :=
    R.tangentPaperCleanCommonMultiplierList_card_lower_of_headCandidate
      (W := W) (K := K) (h := h) (Phead := roughHeadModulus W)
        (X0 := X0) (u := u) (v := v) certificate fixedExceptional
        hfixedTail hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime
        (candidateLower := tangentRoughHeadCandidateLower W n K h u v)
        (exceptionalUpper := tangentCanonicalExceptionalNatUpper
          n K h X0 (yNat n) u v)
        (lowerCard := tangentEffectiveLowerCard density n v)
        hcandidate (hexceptional K h X0 u v huPrime.pos hvPrime.pos)
        harithmetic
  have hscaleV := tangentEffectiveLowerCard_scale
    (density := density) (n := n) (smallerLabel := v) hvPrime.pos
  have hlowerPos : 0 < tangentEffectiveLowerCard density n v := by
    unfold tangentEffectiveLowerCard
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos hdensity (by exact_mod_cast hn))
      (by exact_mod_cast hvPrime.pos)
  have hscaleU :
      density * (n : ℝ) ≤
        (tangentEffectiveLowerCard density n v : ℝ) * u := by
    exact hscaleV.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hvu) (Nat.cast_nonneg _))
  exact ⟨hlowerPos, hlower, hscaleU, hscaleV⟩

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalDistributedTangentBridge -/
section


/-!
# Canonical selector boundary through a distributed tangent flow

This is the star-free replacement for the boundary portion of
`BankPaperCanonicalTangentResidualBridge`.  A distributed earthmover with
the literal canonical residual has the exact factorization boundary needed
by `tangentUpdate_valuation_eq_target`; equal request splitting preserves it.

No clean-list estimate or final collision conclusion occurs in this module.
The only collision-facing asymptotic recorded here is the unconditional
dense-support ceiling `yNat^3 / n -> 0`.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section











/-- Canonical-label specialization of the numerical ratio locality theorem.
The only remaining input is the honest geometry statement for the chosen
fixed-ratio cells. -/
theorem bankPaperCanonical_ratioCellEarthmover_positiveEdge_locality
    {n W : Nat} {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (ratioUpper : Real)
    (hgeometry : TangentRatioCellGeometry
      bankPaperCanonicalTangentPrimeLabel bandOf cellIndex ratioUpper)
    {edge : BankPaperCanonicalTangentPrime n W ×
        BankPaperCanonicalTangentPrime n W}
    (hedge : edge ∈ tangentPositiveFlowEdges
      (tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex)) :
    (((max (bankPaperCanonicalTangentPrimeLabel edge.1)
          (bankPaperCanonicalTangentPrimeLabel edge.2) : Nat) : Real) /
      ((min (bankPaperCanonicalTangentPrimeLabel edge.1)
          (bankPaperCanonicalTangentPrimeLabel edge.2) : Nat) : Real)) <=
        ratioUpper := by
  exact tangentRatioCellEarthmoverFlow_positiveEdge_locality
    lastCell residual bankPaperCanonicalTangentPrimeLabel
      bandOf cellIndex ratioUpper hgeometry hedge

/-! ## Canonical notation for an arbitrary distributed flow -/

















/-! ## Selector bounds converted to the literal cell ledgers -/









/-! ## The explicit ratio-cell flow, rather than a supplied flow -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentPaperCleanListAbsorption -/
section


/-!
# Closing the paper-scale tangent clean-list inequality

This file fixes the moving parameters used in Section 9 of the paper:

* `h = upperTailLength c n = ceil(c n / log n)`;
* `Phead = roughHeadModulus W`;
* `X0 = ceil(n ^ deltaStar)`;
* `y = yNat n = floor(n ^ (2/9))`;
* `W < v <= u <= y` and `u / v <= r0 < 3/2`.

For fixed `W`, `K`, `c`, `r0`, and `deltaStar`, the head-density gap is

`roughHeadDensity W * (2 - r0)`.

We reserve one sixteenth of that gap as the effective list density.  A
slightly conservative explicit version of the paper's one-time cutoff makes
the canonical Selberg main term at most one quarter of the gap.  The
Lambda-squared endpoint remainder and the sharp bank deletion census are
then `o(n/u)`, uniformly for `u <= yNat n`.  The fixed-modulus endpoint loss,
the natural floors and ceilings, and `K*h` are absorbed at the same scale.

Consequently the final candidate-floor-versus-loss inequality is proved
eventually; it is not retained as a premise of the paper-facing wrapper.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Literal Section 9 parameters -/







/-- The fixed-head gap is positive whenever the endpoint-ratio cap is below
two. -/
theorem tangentPaperHeadGap_pos
    (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperHeadGap W r0 := by
  unfold tangentPaperHeadGap
  exact mul_pos (roughHeadDensity_pos W) (sub_pos.mpr hr0)

/-- The retained one-sixteenth clean-list density is positive under the same
ratio cap. -/
theorem tangentPaperCleanListDensity_pos
    (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperCleanListDensity W r0 := by
  unfold tangentPaperCleanListDensity
  exact div_pos (tangentPaperHeadGap_pos W hr0) (by norm_num)











/-! ## The harmonic main term -/





/-! ## Moving-scale negligibility -/





/-! ## Eventual exceptional-loss absorption -/





/-! ## The fixed-head candidate at the paper endpoints -/





/-! ## The literal candidate floor absorbs every canonical loss -/



/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization

/-- The sharp-bank clean-list wrapper with all Section 9 numerical choices
fixed literally.  In contrast with the preceding canonical wrapper, this
wrapper has no candidate interval or candidate-floor-versus-loss premise:
both are supplied uniformly by
`eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses`. -/
theorem eventually_tangentPaperCleanCommonMultiplierList_card_lower_absorbed
    (W K : ℕ) {tailC r0 deltaStar : ℝ}
    (htailC : 0 < tailC) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (anchorC : ℝ) (depth M u v : ℕ)
        (left right : ℕ → ℕ) (changed : Finset ℕ),
      ∀ (R : BankPaperRealization n M)
        (certificate : GuardedCentralAnchorCertificate anchorC depth n
          left right changed)
        (fixedExceptional : Finset ℕ),
      fixedExceptional ⊆ Finset.Ioc (2 * n) M →
      2 ≤ W → 2 * depth + 1 ≤ W →
      W < v → v ≤ u → u ≤ yNat n →
      yNat n < centralAnchorCutoff depth n →
      u.Prime → v.Prime →
      (u : ℝ) / (v : ℝ) ≤ r0 →
      0 < tangentEffectiveLowerCard
        (tangentPaperCleanListDensity W r0) n v ∧
      tangentEffectiveLowerCard
          (tangentPaperCleanListDensity W r0) n v ≤
        (tangentCleanCommonMultiplierList n K (upperTailLength tailC n)
          (roughHeadModulus W)
          (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional)).card ∧
      tangentPaperCleanListDensity W r0 * n ≤
        (tangentEffectiveLowerCard
          (tangentPaperCleanListDensity W r0) n v : ℝ) * u ∧
      tangentPaperCleanListDensity W r0 * n ≤
        (tangentEffectiveLowerCard
          (tangentPaperCleanListDensity W r0) n v : ℝ) * v := by
  have hcanonical :=
    eventually_tangentPaperCleanCommonMultiplierList_card_lower_canonical
  have habsorption :=
    eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses
      W K htailC hr0one hr0three hdelta hdeltaUpper hmainSmall
  filter_upwards [hcanonical, habsorption]
    with n hcanonicalN habsorptionN
  intro anchorC depth M u v left right changed R certificate fixedExceptional
    hfixedTail hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime hratio
  have hdensity : 0 < tangentPaperCleanListDensity W r0 :=
    tangentPaperCleanListDensity_pos W (hr0three.trans (by norm_num))
  have harithmetic :=
    habsorptionN u v huPrime.pos hvPrime.pos hvu huy hratio
  exact hcanonicalN anchorC depth M W K (upperTailLength tailC n)
    (tangentPaperExceptionalCutoff deltaStar n) u v left right changed
    R certificate fixedExceptional (tangentPaperCleanListDensity W r0)
    hfixedTail hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime
    hdensity harithmetic.1 harithmetic.2

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalDistributedCleanListAdapter -/
section


/-!
# Distributed canonical clean-list adapter

The absorbed clean-list theorem is uniform in every permitted unordered
prime pair `(u,v)`, whereas the distributed tangent assembly indexes its
lists by split requests of the explicit ratio-cell earthmover.  This module
performs only that finite reindexing.

For a request, its two endpoint labels are prime-band members.  Their
maximum and minimum therefore satisfy all elementary prime and cutoff
conditions of the absorbed theorem.  `TangentRatioCellGeometry` supplies
the sole nontrivial conversion: positive earthmover support has endpoint
ratio at most `r0`.  No list estimate, cell occupancy statement, traffic
bound, or selector slack is assumed or reproved here.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-- The paper clean-list lower bound, positivity, and endpoint scale for
every split request of the explicit distributed ratio-cell earthmover.

All analytic losses are already absorbed by
`eventually_tangentPaperCleanCommonMultiplierList_card_lower_absorbed`.
The additional input here is exactly the fixed-ratio geometry needed to
show that the two labels underlying each positive-flow request form a
permitted pair. -/
theorem eventually_canonicalDistributedSectionNineCleanListLower_absorbed
    (W K : Nat) {c r0 deltaStar : Real}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : Nat in atTop,
      ∀ (depth : Nat) (left right : Nat → Nat)
        (changed : Finset Nat),
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed)
        (fixedExceptional : Finset Nat),
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band],
      ∀ (lastCell : Band → Nat)
        (residual : BankPaperCanonicalTangentPrime n W → Real)
        (bandOf : BankPaperCanonicalTangentPrime n W → Band)
        (cellIndex : BankPaperCanonicalTangentPrime n W → Nat)
        (L sigma : Real),
      fixedExceptional ⊆
          Finset.Ioc (2 * n) (upperEndpoint n (upperTailLength c n)) →
      2 ≤ W → 2 * depth + 1 ≤ W →
      yNat n < centralAnchorCutoff depth n →
      TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
        bandOf cellIndex r0 →
      (∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell residual
            bandOf cellIndex) L sigma,
        0 < bankPaperCanonicalDistributedTangentLowerCard
          (density := tangentPaperCleanListDensity W r0) request) ∧
      (∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell residual
            bandOf cellIndex) L sigma,
        bankPaperCanonicalDistributedTangentLowerCard
            (density := tangentPaperCleanListDensity W r0) request ≤
          (tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges
              (tangentRatioCellEarthmoverFlow lastCell residual
                bandOf cellIndex))
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (fun edge : BankPaperCanonicalTangentPrime n W ×
                BankPaperCanonicalTangentPrime n W =>
              tangentRatioCellEarthmoverFlow lastCell residual
                bandOf cellIndex edge.1 edge.2)
            n K (upperTailLength c n) (roughHeadModulus W)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request).card) ∧
      ∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell residual
            bandOf cellIndex) L sigma,
        ∀ side,
          tangentPaperCleanListDensity W r0 * n ≤
            (bankPaperCanonicalDistributedTangentLowerCard
              (density := tangentPaperCleanListDensity W r0)
              request : Real) *
              tangentEndpointLabel
                bankPaperCanonicalDistributedTangentRequestSource
                bankPaperCanonicalDistributedTangentRequestTarget
                side request := by
  have hclean :=
    eventually_tangentPaperCleanCommonMultiplierList_card_lower_absorbed
      W K hc hr0one hr0three hdelta hdeltaUpper hmainSmall
  filter_upwards [hclean] with n hcleanN
  intro depth left right changed R certificate fixedExceptional
    Band _instBandFintype _instBandDecidable
    lastCell residual bandOf cellIndex L sigma
    hfixedTail hTwoW hPrefix hyCutoff hgeometry
  let flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real :=
    tangentRatioCellEarthmoverFlow lastCell residual bandOf cellIndex
  let edges := tangentPositiveFlowEdges flow
  let source := tangentStarEdgeSource
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let target := tangentStarEdgeTarget
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let edgeFlow :
      BankPaperCanonicalTangentPrime n W ×
          BankPaperCanonicalTangentPrime n W → Real :=
    fun edge => flow edge.1 edge.2
  let requestSource :=
    tangentSplitRequestSource
      (edges := edges) (L := L) (sigma := sigma) (flow := edgeFlow) source
  let requestTarget :=
    tangentSplitRequestTarget
      (edges := edges) (L := L) (sigma := sigma) (flow := edgeFlow) target
  have hrequestPrime :
      ∀ request : TangentSplitRequest edges L sigma edgeFlow,
        (requestSource request).Prime ∧
          (requestTarget request).Prime := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.2
  have hrequestBand :
      ∀ request : TangentSplitRequest edges L sigma edgeFlow,
        (W < requestSource request ∧
            requestSource request ≤ yNat n) ∧
          (W < requestTarget request ∧
            requestTarget request ≤ yNat n) := by
    intro request
    constructor
    · constructor
      · simpa only [requestSource, source, tangentSplitRequestSource,
          tangentSplitRequestEdge, tangentStarEdgeSource] using
          cutoff_lt_of_mem_primeBand request.1.1.1.2
      · simpa only [requestSource, source, tangentSplitRequestSource,
          tangentSplitRequestEdge, tangentStarEdgeSource] using
          le_yNat_of_mem_primeBand request.1.1.1.2
    · constructor
      · simpa only [requestTarget, target, tangentSplitRequestTarget,
          tangentSplitRequestEdge, tangentStarEdgeTarget] using
          cutoff_lt_of_mem_primeBand request.1.1.2.2
      · simpa only [requestTarget, target, tangentSplitRequestTarget,
          tangentSplitRequestEdge, tangentStarEdgeTarget] using
          le_yNat_of_mem_primeBand request.1.1.2.2
  have hcleanData :
      ∀ request : TangentSplitRequest edges L sigma edgeFlow,
        0 < tangentEffectiveLowerCard
            (tangentPaperCleanListDensity W r0) n
            (min (requestSource request) (requestTarget request)) ∧
          tangentEffectiveLowerCard
              (tangentPaperCleanListDensity W r0) n
              (min (requestSource request) (requestTarget request)) ≤
            (tangentCleanCommonMultiplierList n K
              (upperTailLength c n) (roughHeadModulus W)
              (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
              (max (requestSource request) (requestTarget request))
              (min (requestSource request) (requestTarget request))
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional)).card ∧
          tangentPaperCleanListDensity W r0 * n ≤
            (tangentEffectiveLowerCard
              (tangentPaperCleanListDensity W r0) n
              (min (requestSource request)
                (requestTarget request)) : Real) *
              max (requestSource request) (requestTarget request) ∧
          tangentPaperCleanListDensity W r0 * n ≤
            (tangentEffectiveLowerCard
              (tangentPaperCleanListDensity W r0) n
              (min (requestSource request)
                (requestTarget request)) : Real) *
              min (requestSource request) (requestTarget request) := by
    intro request
    let u := max (requestSource request) (requestTarget request)
    let v := min (requestSource request) (requestTarget request)
    have huPrime : u.Prime := by
      rcases le_total (requestSource request) (requestTarget request) with
        hst | hts
      · simpa only [u, max_eq_right hst] using
          (hrequestPrime request).2
      · simpa only [u, max_eq_left hts] using
          (hrequestPrime request).1
    have hvPrime : v.Prime := by
      rcases le_total (requestSource request) (requestTarget request) with
        hst | hts
      · simpa only [v, min_eq_left hst] using
          (hrequestPrime request).1
      · simpa only [v, min_eq_right hts] using
          (hrequestPrime request).2
    have hWv : W < v :=
      lt_min (hrequestBand request).1.1 (hrequestBand request).2.1
    have hvu : v ≤ u := min_le_max
    have huy : u ≤ yNat n :=
      max_le (hrequestBand request).1.2 (hrequestBand request).2.2
    have hedge : request.1.1 ∈ tangentPositiveFlowEdges
        (tangentRatioCellEarthmoverFlow lastCell residual
          bandOf cellIndex) := by
      simpa only [edges, flow] using request.1.2
    have hratioEdge :=
      bankPaperCanonical_ratioCellEarthmover_positiveEdge_locality
        lastCell residual bandOf cellIndex r0 hgeometry hedge
    have hratio : (u : Real) / (v : Real) ≤ r0 := by
      simpa only [u, v, requestSource, requestTarget, source, target,
        tangentSplitRequestSource, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeSource,
        tangentStarEdgeTarget] using hratioEdge
    exact hcleanN c depth
      (upperEndpoint n (upperTailLength c n)) u v left right changed
      R certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
      hyCutoff huPrime hvPrime hratio
  constructor
  · intro request
    simpa only [bankPaperCanonicalDistributedTangentLowerCard,
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget,
      requestSource, requestTarget, edges, source, target, edgeFlow, flow]
      using (hcleanData request).1
  constructor
  · intro request
    simpa only [bankPaperCanonicalDistributedTangentLowerCard,
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget,
      tangentSplitCleanMultiplierLists, tangentCleanMultiplierLists,
      requestSource, requestTarget, edges, source, target, edgeFlow, flow]
      using (hcleanData request).2.1
  · intro request side
    have hminScale := (hcleanData request).2.2.2
    cases side with
    | source =>
        have hminSource :
            ((min (requestSource request) (requestTarget request) : Nat) :
                Real) <= (requestSource request : Real) := by
          exact_mod_cast
            (min_le_left (requestSource request) (requestTarget request))
        have hscale := hminScale.trans
          (mul_le_mul_of_nonneg_left
            hminSource
            (Nat.cast_nonneg _))
        simpa only [bankPaperCanonicalDistributedTangentLowerCard,
          bankPaperCanonicalDistributedTangentRequestSource,
          bankPaperCanonicalDistributedTangentRequestTarget,
          tangentEndpointLabel, requestSource, requestTarget, edges,
          source, target, edgeFlow, flow] using hscale
    | target =>
        have hminTarget :
            ((min (requestSource request) (requestTarget request) : Nat) :
                Real) <= (requestTarget request : Real) := by
          exact_mod_cast
            (min_le_right (requestSource request) (requestTarget request))
        have hscale := hminScale.trans
          (mul_le_mul_of_nonneg_left
            hminTarget
            (Nat.cast_nonneg _))
        simpa only [bankPaperCanonicalDistributedTangentLowerCard,
          bankPaperCanonicalDistributedTangentRequestSource,
          bankPaperCanonicalDistributedTangentRequestTarget,
          tangentEndpointLabel, requestSource, requestTarget, edges,
          source, target, edgeFlow, flow] using hscale

end BankPaperRealization

/-! ## Harmonic pointwise specialization -/



end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal004_015.{u_1} := by
  exact @Erdos390.WholePaper.BankPaperRealization.eventually_canonicalDistributedSectionNineCleanListLower_absorbed
