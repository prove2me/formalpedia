-- Prove2me | solution 1 for Erdos390.WholePaper.eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:06:06.470759+00:00
-- url     : https://prove2.me/submissions/0248d87f-9644-4c63-9e01-a1adfe51fce5

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






















































/-- The integral cutoff `floor(n^(2/9))` retains enough logarithmic size
for the complete four-mark coordinate range. -/
theorem eventually_one_fifth_L_le_log_yNat :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually
      (Filter.eventually_ge_atTop (45 * Real.log 2))] with n hn hyn hLn
  have hypos : 0 < y n := y_pos hn
  have hyNatLower : y n / 2 ≤ (yNat n : ℝ) := by
    have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogLower : Real.log (y n / 2) ≤ Real.log (yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    (1 / 5 : ℝ) * L n ≤ Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      linarith
    _ ≤ Real.log (yNat n : ℝ) := hlogLower






end Erdos390.Full.FriableAsymptotic

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

/-- Hence the chosen tail length is eventually at most `n`. -/
theorem eventually_upperTailLength_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, upperTailLength c n ≤ n := by
  have hsmall := (upperTailLength_ratio_tendsto_zero hc).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratio hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcast : (upperTailLength c n : ℝ) ≤ (n : ℝ) := by
    have hratioLe :
        (upperTailLength c n : ℝ) / (n : ℝ) ≤ 1 := hratio.le
    have := (div_le_iff₀ hnReal).mp hratioLe
    simpa only [one_mul] using this
  exact_mod_cast hcast



















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

















/-! ## Explicit fixed-period error -/







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





theorem paperExceptionalUpperFactors_subset_upperBlock
    (n h : ℕ) (deltaStar : ℝ) :
    paperExceptionalUpperFactors n h deltaStar ⊆
      roughUpperBlock n h :=
  Finset.filter_subset _ _

namespace BankPaperRealization



























end BankPaperRealization

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



/-- The smooth cutoff tends to infinity, exposed here because a fixed anchor
prefix contributes only the cofactors `1,…,2*depth+1`. -/
theorem bankAnchor_yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy







/-! ## Arithmetic collision kernels -/



namespace BankPaperRealization



/-! ## Literal recovery of the incident cores from actual requests -/





















/-! ## Complete finite collision theorem -/





end BankPaperRealization

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























/-! ## Substitution of the verified abstract sieve bound -/

















/-! ## The `delta_* < 1/18`, `y^4=n^(8/9)` remainder arithmetic -/









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

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalValuationFibers -/
section


/-!
# Finite valuation fibres for the literal fixed exceptional factors

This file gives the first finite low-prime bridge for the paper's literal
fixed exceptional set.  The exceptional upper factors are partitioned by
their complete smooth part at the canonical cutoff `yNat n`.  At a prime
`p ≤ yNat n`, the factorization charge is therefore the corresponding
smooth-part valuation times the size of each fibre.

Each actual fibre injects, by its complete rough label, into the physical
reduced-residue interval obtained by dividing `(2n,2n+h]` by that smooth
part.  The last theorem substitutes the already proved canonical finite
Selberg estimate for these candidate intervals.  No smooth-number census,
valuation-sum estimate, or asymptotic exceptional-charge bound is asserted
here.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Canonical smooth fibres and their rough candidates -/













/-- Every literal exceptional upper factor is positive. -/
theorem paperExceptionalUpperFactors_pos
    {n h a : ℕ} {deltaStar : ℝ}
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    0 < a := by
  have haInterval : a ∈ Finset.Ioc (2 * n) (2 * n + h) := by
    simpa only [roughUpperBlock] using
      (paperExceptionalUpperFactors_subset_upperBlock n h deltaStar ha)
  exact lt_of_le_of_lt (Nat.zero_le (2 * n))
    (Finset.mem_Ioc.mp haInterval).1

/-! ## Exact low-prime valuation partition -/

/-- At a low prime, the full literal exceptional product has exactly the
smooth-part weighted fibre decomposition. -/
theorem paperExceptionalUpperFactors_prod_factorization_eq_smoothFiberSum
    {n h p : ℕ} {deltaStar : ℝ} (hp : p ≤ yNat n) :
    ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p =
      ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
        b.factorization p *
          (paperExceptionalSmoothFiber n h deltaStar b).card := by
  have hfactorization :
      ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p =
        ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          a.factorization p :=
    Nat.factorization_prod_apply
      (fun a ha ↦ (paperExceptionalUpperFactors_pos ha).ne')
  rw [hfactorization]
  calc
    (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        a.factorization p) =
        ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          (completeSmoothPart (yNat n) a).factorization p := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [completeSmoothPart_factorization_apply, if_pos hp]
    _ = ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
          ∑ a ∈ paperExceptionalSmoothFiber n h deltaStar b,
            (completeSmoothPart (yNat n) a).factorization p := by
      symm
      simpa only [paperExceptionalSmoothParts,
        paperExceptionalSmoothFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (s := paperExceptionalUpperFactors n h deltaStar)
          (t := (paperExceptionalUpperFactors n h deltaStar).image
            (completeSmoothPart (yNat n)))
          (g := completeSmoothPart (yNat n))
          (fun a ha ↦ Finset.mem_image_of_mem
            (completeSmoothPart (yNat n)) ha)
          (fun a ↦ (completeSmoothPart (yNat n) a).factorization p))
    _ = ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
          b.factorization p *
            (paperExceptionalSmoothFiber n h deltaStar b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ a ∈ paperExceptionalSmoothFiber n h deltaStar b,
            (completeSmoothPart (yNat n) a).factorization p) =
            (paperExceptionalSmoothFiber n h deltaStar b).card *
              b.factorization p := by
          apply Finset.sum_const_nat
          intro a ha
          rw [(mem_paperExceptionalSmoothFiber.mp ha).2]
        _ = b.factorization p *
              (paperExceptionalSmoothFiber n h deltaStar b).card :=
          Nat.mul_comm _ _

/-! ## Injection of each actual fibre into a reduced-residue interval -/

/-- Fixing the smooth part makes the complete rough label injective on one
literal exceptional fibre. -/
theorem completeRoughLabel_injOn_paperExceptionalSmoothFiber
    {n h b : ℕ} {deltaStar : ℝ} :
    Set.InjOn (completeRoughLabel (yNat n))
      (paperExceptionalSmoothFiber n h deltaStar b : Set ℕ) := by
  intro a₁ ha₁ a₂ ha₂ hrough
  have hsmooth₁ := (mem_paperExceptionalSmoothFiber.mp ha₁).2
  have hsmooth₂ := (mem_paperExceptionalSmoothFiber.mp ha₂).2
  calc
    a₁ = completeRoughLabel (yNat n) a₁ *
        completeSmoothPart (yNat n) a₁ :=
      (completeRoughLabel_mul_completeSmoothPart (yNat n) a₁).symm
    _ = completeRoughLabel (yNat n) a₂ *
        completeSmoothPart (yNat n) a₂ := by
      rw [hrough, hsmooth₁, hsmooth₂]
    _ = a₂ := completeRoughLabel_mul_completeSmoothPart (yNat n) a₂

/-- A complete rough label from an actual smooth fibre lies in its claimed
physical reduced-residue interval. -/
theorem completeRoughLabel_mem_paperExceptionalRoughCandidates
    {n h a b : ℕ} {deltaStar : ℝ}
    (ha : a ∈ paperExceptionalSmoothFiber n h deltaStar b) :
    completeRoughLabel (yNat n) a ∈
      paperExceptionalRoughCandidates n h (yNat n) b := by
  have haData := mem_paperExceptionalSmoothFiber.mp ha
  have haBounds : 2 * n < a ∧ a ≤ 2 * n + h := by
    simpa only [roughUpperBlock, Finset.mem_Ioc] using
      (mem_paperExceptionalUpperFactors.mp haData.1).1
  have haPos : 0 < a := paperExceptionalUpperFactors_pos haData.1
  have hbPos : 0 < b := by
    have hsmoothPos := completeSmoothPart_pos
      (y := yNat n) (a := a) haPos
    simpa only [haData.2] using hsmoothPos
  have hdecomp : completeRoughLabel (yNat n) a * b = a := by
    simpa only [haData.2] using
      completeRoughLabel_mul_completeSmoothPart (yNat n) a
  rw [mem_paperExceptionalRoughCandidates]
  refine ⟨?_, ?_, completeRoughLabel_coprime_roughHeadModulus (yNat n) a⟩
  · apply (Nat.div_lt_iff_lt_mul hbPos).mpr
    simpa only [hdecomp] using haBounds.1
  · apply (Nat.le_div_iff_mul_le hbPos).mpr
    simpa only [hdecomp] using haBounds.2

/-- Fibrewise canonical reduction: the actual exceptional fibre injects
into the reduced-residue rough-label interval. -/
theorem paperExceptionalSmoothFiber_card_le_roughCandidates
    {n h b : ℕ} {deltaStar : ℝ} :
    (paperExceptionalSmoothFiber n h deltaStar b).card ≤
      (paperExceptionalRoughCandidates n h (yNat n) b).card := by
  calc
    (paperExceptionalSmoothFiber n h deltaStar b).card =
        ((paperExceptionalSmoothFiber n h deltaStar b).image
          (completeRoughLabel (yNat n))).card :=
      (Finset.card_image_of_injOn
        completeRoughLabel_injOn_paperExceptionalSmoothFiber).symm
    _ ≤ (paperExceptionalRoughCandidates n h (yNat n) b).card := by
      apply Finset.card_le_card
      intro r hr
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
      exact completeRoughLabel_mem_paperExceptionalRoughCandidates ha

/-! ## The fixed exceptional product -/

namespace BankPaperRealization

/-- The fixed set difference has no more low-prime charge than the exact
smooth-fibre decomposition of the full literal exceptional set. -/
theorem paperFixedExceptionalFactors_prod_factorization_le_smoothFiberSum
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : ℝ} (hp : p ≤ yNat n) :
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p ≤
      ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
        b.factorization p *
          (paperExceptionalSmoothFiber n h deltaStar b).card := by
  have hsubset : R.paperFixedExceptionalFactors deltaStar ⊆
      paperExceptionalUpperFactors n h deltaStar := by
    intro a ha
    rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at ha
    exact ha.1
  calc
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
        ∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
          a.factorization p := by
      exact Nat.factorization_prod_apply fun a ha ↦
        (paperExceptionalUpperFactors_pos (hsubset ha)).ne'
    _ ≤ ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          a.factorization p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _a _haUpper _haFixed ↦ Nat.zero_le _)
    _ = ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p := by
      symm
      exact Nat.factorization_prod_apply fun a ha ↦
        (paperExceptionalUpperFactors_pos ha).ne'
    _ = ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
          b.factorization p *
            (paperExceptionalSmoothFiber n h deltaStar b).card :=
      paperExceptionalUpperFactors_prod_factorization_eq_smoothFiberSum hp



end BankPaperRealization

/-! ## Canonical Selberg substitution on each candidate interval -/

/-- The existing canonical lambda-square sieve applies verbatim to every
rough-candidate fibre, uniformly in its physical parameters. -/
theorem eventually_paperExceptionalRoughCandidates_card_le_canonicalLambdaSquare :
    ∀ᶠ y : ℕ in atTop, ∀ n h b : ℕ,
      ((paperExceptionalRoughCandidates n h y b).card : ℝ) ≤
        ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (y : ℝ)) +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
            Real.log (y : ℝ) ^ 2) := by
  filter_upwards
    [eventually_reducedResidueIoc_card_le_canonicalLambdaSquare_roughHead]
      with y hy
  intro n h b
  simpa only [paperExceptionalRoughCandidates] using
    hy ((2 * n) / b) ((2 * n + h) / b)

/-- At the paper's canonical cutoff, every actual smooth fibre inherits the
canonical lambda-square interval estimate. -/
theorem eventually_paperExceptionalSmoothFiber_card_le_canonicalLambdaSquare :
    ∀ᶠ n : ℕ in atTop, ∀ h b : ℕ, ∀ deltaStar : ℝ,
      ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
        ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (yNat n : ℝ)) +
          tangentSelbergCanonicalLambdaConstant ^ 2 *
              (yNat n : ℝ) ^ 4 /
            Real.log (yNat n : ℝ) ^ 2) := by
  filter_upwards
    [bankAnchor_yNat_tendsto_atTop.eventually
      eventually_paperExceptionalRoughCandidates_card_le_canonicalLambdaSquare]
      with n hn
  intro h b deltaStar
  have hcardCast :
      ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
        ((paperExceptionalRoughCandidates n h (yNat n) b).card : ℝ) := by
    exact_mod_cast
      (paperExceptionalSmoothFiber_card_le_roughCandidates
        (n := n) (h := h) (b := b) (deltaStar := deltaStar))
  exact hcardCast.trans (hn n h b)

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ExceptionalValuationSums -/
section


/-!
# Elementary finite valuation sums

This file records the two elementary estimates used when a fixed exceptional
integer contributes a factorization-coordinate charge (the `p`-adic charge
when `p` is prime).  The unweighted prefix is exactly the corresponding
factorization coordinate of a factorial.  Discrete summation by parts then
converts the same prefix estimate into a harmonic weighted bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The total factorization coordinate of the positive integers at most `B`
is the same coordinate of `B!`.  For prime `p`, this is the usual `p`-adic
valuation identity; primality is not needed for the factorization identity. -/
theorem sum_factorization_Icc_eq_factorialFactorization (p B : ℕ) :
    (∑ b ∈ Finset.Icc 1 B, b.factorization p) =
      B.factorial.factorization p := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [← Finset.prod_Ico_id_eq_factorial]
  exact (Nat.factorization_prod_apply fun b hb ↦
    (Nat.ne_of_gt (Finset.mem_Ico.mp hb).1)).symm

/-- Natural-valued Legendre bound for the total valuation of
`1, ..., B`. -/
theorem sum_factorization_Icc_le_div_pred {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, b.factorization p) ≤ B / (p - 1) := by
  rw [sum_factorization_Icc_eq_factorialFactorization]
  exact Nat.factorization_factorial_le_div_pred hp B

/-- Real version of the elementary Legendre prefix bound. -/
theorem sum_factorization_Icc_cast_le_div_pred {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
      (B : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  calc
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) =
        ((∑ b ∈ Finset.Icc 1 B, b.factorization p : ℕ) : ℝ) := by
      simp only [Nat.cast_sum]
    _ ≤ ((B / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast sum_factorization_Icc_le_div_pred hp
    _ ≤ (B : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le







theorem valuationPrefixReal_le_div_pred {p B : ℕ} (hp : p.Prime) :
    valuationPrefixReal p B ≤
      (B : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  simpa only [valuationPrefixReal] using
    sum_factorization_Icc_cast_le_div_pred (p := p) (B := B) hp

/-- A range beginning at zero is the positive valuation prefix because the
factorization of zero is defined to be zero. -/
theorem sum_range_succ_factorization_cast_eq_valuationPrefixReal (p B : ℕ) :
    (∑ b ∈ Finset.range (B + 1), (b.factorization p : ℝ)) =
      valuationPrefixReal p B := by
  rw [Nat.range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero B),
    Nat.add_sub_cancel_right]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le B), Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  simp [valuationPrefixReal]

/-- Exact finite Abel identity for the harmonically weighted valuation sum. -/
theorem weightedFactorizationSum_eq_abel {p B : ℕ} (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (1 / (b : ℝ)) * (b.factorization p : ℝ)) =
      (1 / (B : ℝ)) * valuationPrefixReal p B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b := by
  have hBpos : 0 < B := by omega
  have habel := Finset.sum_Ioc_by_parts
    (f := fun b : ℕ ↦ 1 / (b : ℝ))
    (g := fun b : ℕ ↦ (b.factorization p : ℝ))
    (m := 0) (n := B) hBpos
  have hIoc : Finset.Ioc 0 B = Finset.Icc 1 B := by
    simpa only [zero_add] using
      (Finset.Icc_add_one_left_eq_Ioc 0 B).symm
  rw [hIoc] at habel
  simp_rw [sum_range_succ_factorization_cast_eq_valuationPrefixReal] at habel
  simp only [smul_eq_mul, zero_add, Nat.cast_one, div_one,
    valuationPrefixReal_zero, mul_zero, sub_zero] at habel
  have hneg :
      -(∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / ((b + 1 : ℕ) : ℝ) - 1 / (b : ℝ)) *
            valuationPrefixReal p b) =
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (1 / (b : ℝ)) * (b.factorization p : ℝ)) =
        (1 / (B : ℝ)) * valuationPrefixReal p B -
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            (1 / ((b + 1 : ℕ) : ℝ) - 1 / (b : ℝ)) *
              valuationPrefixReal p b := habel
    _ = _ := by rw [sub_eq_add_neg, hneg]

private theorem one_add_sum_Ioc_succ_reciprocal_eq_harmonic
    {B : ℕ} (hB : 1 ≤ B) :
    1 + ∑ b ∈ Finset.Ioc 0 (B - 1),
        1 / ((b + 1 : ℕ) : ℝ) = (harmonic B : ℝ) := by
  have hset : Finset.Ioc 0 (B - 1) = Finset.Ico 1 B := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel hB]
    simp
  have hshift :
      (∑ b ∈ Finset.Ico 1 B, 1 / ((b + 1 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.Ico 2 (B + 1), 1 / (k : ℝ) := by
    simpa only [one_add_one_eq_two] using
      (Finset.sum_Ico_add' (fun k : ℕ ↦ 1 / (k : ℝ)) 1 B 1)
  rw [hset, hshift, Finset.Ico_add_one_right_eq_Icc]
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [Finset.Icc_eq_cons_Ioc hB, Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  norm_num

/-- Sharp elementary harmonic bound for the weighted valuation sum. -/
theorem weightedFactorizationSum_le_one_add_log_div_pred
    {p B : ℕ} (hp : p.Prime) (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
      (1 + Real.log (B : ℝ)) / ((p - 1 : ℕ) : ℝ) := by
  have hdNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hd : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hdNat
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hend :
      (1 / (B : ℝ)) * valuationPrefixReal p B ≤
        1 / ((p - 1 : ℕ) : ℝ) := by
    calc
      (1 / (B : ℝ)) * valuationPrefixReal p B ≤
          (1 / (B : ℝ)) *
            ((B : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (valuationPrefixReal_le_div_pred hp)
          (one_div_nonneg.mpr hBreal.le)
      _ = 1 / ((p - 1 : ℕ) : ℝ) := by
        field_simp [ne_of_gt hBreal, ne_of_gt hd]
  have hterm (b : ℕ) (hb : b ∈ Finset.Ioc 0 (B - 1)) :
      (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
          valuationPrefixReal p b ≤
        (1 / ((p - 1 : ℕ) : ℝ)) *
          (1 / ((b + 1 : ℕ) : ℝ)) := by
    have hbNat : 0 < b := (Finset.mem_Ioc.mp hb).1
    have hbReal : 0 < (b : ℝ) := by exact_mod_cast hbNat
    have hbSuccReal : 0 < ((b + 1 : ℕ) : ℝ) := by positivity
    have hdiff :
        0 ≤ 1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) := by
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hbReal (by
        exact_mod_cast Nat.le_add_right b 1))
    calc
      (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
          valuationPrefixReal p b ≤
        (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
          ((b : ℝ) / ((p - 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (valuationPrefixReal_le_div_pred hp) hdiff
      _ = (1 / ((p - 1 : ℕ) : ℝ)) *
          (1 / ((b + 1 : ℕ) : ℝ)) := by
        push_cast
        field_simp [ne_of_gt hbReal, ne_of_gt hbSuccReal, ne_of_gt hd]
        ring
  have hinterior :
      (∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b) ≤
        (1 / ((p - 1 : ℕ) : ℝ)) *
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            1 / ((b + 1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb ↦ hterm b hb
  have hharm : (harmonic B : ℝ) ≤ 1 + Real.log (B : ℝ) :=
    harmonic_le_one_add_log B
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) =
        ∑ b ∈ Finset.Icc 1 B,
          (1 / (b : ℝ)) * (b.factorization p : ℝ) := by
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = (1 / (B : ℝ)) * valuationPrefixReal p B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b := weightedFactorizationSum_eq_abel hB
    _ ≤ 1 / ((p - 1 : ℕ) : ℝ) +
        (1 / ((p - 1 : ℕ) : ℝ)) *
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            1 / ((b + 1 : ℕ) : ℝ) := add_le_add hend hinterior
    _ = (1 / ((p - 1 : ℕ) : ℝ)) * (harmonic B : ℝ) := by
      rw [← one_add_sum_Ioc_succ_reciprocal_eq_harmonic hB]
      ring
    _ ≤ (1 / ((p - 1 : ℕ) : ℝ)) *
        (1 + Real.log (B : ℝ)) :=
      mul_le_mul_of_nonneg_left hharm (one_div_nonneg.mpr hd.le)
    _ = (1 + Real.log (B : ℝ)) /
        ((p - 1 : ℕ) : ℝ) := by ring

/-- For primes, the `1/(p-1)` form costs at most a factor two compared with
`1/p`. -/
theorem one_div_prime_pred_le_two_div_prime {p : ℕ} (hp : p.Prime) :
    1 / ((p - 1 : ℕ) : ℝ) ≤ 2 / (p : ℝ) := by
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hdNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hd : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hdNat
  apply (div_le_div_iff₀ hd hpReal).2
  norm_num only [one_mul]
  exact_mod_cast (show p ≤ 2 * (p - 1) by omega)

/-- Convenient `O(B/p)` version of the unweighted valuation bound. -/
theorem sum_factorization_Icc_cast_le_two_mul_div_prime
    {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
      2 * (B : ℝ) / (p : ℝ) := by
  calc
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
        (B : ℝ) / ((p - 1 : ℕ) : ℝ) :=
      sum_factorization_Icc_cast_le_div_pred hp
    _ = (B : ℝ) * (1 / ((p - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (B : ℝ) * (2 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_div_prime_pred_le_two_div_prime hp)
        (Nat.cast_nonneg B)
    _ = 2 * (B : ℝ) / (p : ℝ) := by ring

/-- Convenient uniform `O((1 + log B)/p)` version of the weighted bound. -/
theorem weightedFactorizationSum_le_two_mul_one_add_log_div_prime
    {p B : ℕ} (hp : p.Prime) (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
      2 * (1 + Real.log (B : ℝ)) / (p : ℝ) := by
  have hlog : 0 ≤ 1 + Real.log (B : ℝ) := by
    have hcast : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have hlogNonneg : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hcast
    linarith
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
        (1 + Real.log (B : ℝ)) / ((p - 1 : ℕ) : ℝ) :=
      weightedFactorizationSum_le_one_add_log_div_pred hp hB
    _ = (1 + Real.log (B : ℝ)) *
        (1 / ((p - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (1 + Real.log (B : ℝ)) * (2 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_div_prime_pred_le_two_div_prime hp) hlog
    _ = 2 * (1 + Real.log (B : ℝ)) / (p : ℝ) := by ring

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











/-- The natural ceiling dominates the literal real exceptional cutoff. -/
theorem tangentPaperExceptionalCutoff_cast_ge
    (deltaStar : ℝ) (n : ℕ) :
    (n : ℝ) ^ deltaStar ≤
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) := by
  unfold tangentPaperExceptionalCutoff
  exact Nat.le_ceil _

/-- The safe ceiling changes the paper's real cutoff by strictly less than
one. -/
theorem tangentPaperExceptionalCutoff_cast_lt_add_one
    (deltaStar : ℝ) (n : ℕ) :
    (tangentPaperExceptionalCutoff deltaStar n : ℝ) <
      (n : ℝ) ^ deltaStar + 1 := by
  unfold tangentPaperExceptionalCutoff
  exact Nat.ceil_lt_add_one
    (Real.rpow_nonneg (Nat.cast_nonneg n) deltaStar)



/-- A nonnegative exponent and positive base make the natural exceptional
cutoff strictly positive. -/
theorem tangentPaperExceptionalCutoff_pos
    {deltaStar : ℝ} (hdelta : 0 ≤ deltaStar)
    {n : ℕ} (hn : 1 ≤ n) :
    0 < tangentPaperExceptionalCutoff deltaStar n := by
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast hn) hdelta
  have hceil := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  have hcast : (1 : ℝ) ≤
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) := hone.trans hceil
  have hnat : 1 ≤ tangentPaperExceptionalCutoff deltaStar n := by
    exact_mod_cast hcast
  omega

/-- The ceiling cutoff has logarithm at most the paper exponent term plus
the single `log 2` ceiling loss. -/
theorem tangentPaperExceptionalCutoff_log_le
    {deltaStar : ℝ} (hdelta : 0 ≤ deltaStar)
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
      deltaStar * L n + Real.log 2 := by
  have hcutPos : (0 : ℝ) < tangentPaperExceptionalCutoff deltaStar n := by
    exact_mod_cast tangentPaperExceptionalCutoff_pos hdelta hn
  have hnPos : (0 : ℝ) < n := by positivity
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast hn) hdelta
  have hcutUpper :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        2 * (n : ℝ) ^ deltaStar := by
    calc
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
          (n : ℝ) ^ deltaStar + 1 :=
        (tangentPaperExceptionalCutoff_cast_lt_add_one
          deltaStar n).le
      _ ≤ 2 * (n : ℝ) ^ deltaStar := by linarith
  calc
    Real.log (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        Real.log (2 * (n : ℝ) ^ deltaStar) :=
      Real.log_le_log hcutPos hcutUpper
    _ = deltaStar * L n + Real.log 2 := by
      rw [Real.log_mul (by norm_num)
        (Real.rpow_pos_of_pos hnPos deltaStar).ne',
        Real.log_rpow hnPos]
      unfold L
      ring

/-! ## The harmonic main term -/





/-! ## Moving-scale negligibility -/





/-! ## Eventual exceptional-loss absorption -/





/-! ## The fixed-head candidate at the paper endpoints -/





/-! ## The literal candidate floor absorbs every canonical loss -/



/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalChargeAsymptotic -/
section


/-!
# Asymptotic package for the fixed exceptional low-prime charge

This file records the constants and scale arithmetic used after the finite
weighted Selberg decomposition of `G_fix` has been proved.  In the notation
of the paper,

* `paperExceptionalSelbergMainConstant` is `C_S`;
* `paperExceptionalSelbergRemainderConstant` is `C_R`;
* `paperExceptionalChargeConstant c` is `A_exc(c)`;
* `paperExceptionalChargeEpsilon deltaStar n` is the normalized
  endpoint/remainder coefficient.

The finite majorant below is obtained by composing the separate finite
rough/smooth-fibre argument with the elementary valuation-prefix estimates.
Nothing in this file assumes that the actual exceptional charge satisfies
that majorant.  We prove the finite charge bound and its analytic packaging,
together with the independent arithmetic support fact that, under the
displayed paper-range hypotheses, the actual low-prime charge is exactly
zero above twice the paper's literal real exceptional cutoff.  The
corresponding safe integral-cutoff statement is retained as a corollary.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Auditable paper constants -/











theorem paperExceptionalSelbergMainConstant_pos :
    0 < paperExceptionalSelbergMainConstant := by
  exact tangentSelbergCanonicalMainConstant_pos

theorem paperExceptionalSelbergRemainderConstant_pos :
    0 < paperExceptionalSelbergRemainderConstant := by
  unfold paperExceptionalSelbergRemainderConstant
  exact add_pos_of_nonneg_of_pos (sq_nonneg _)
    paperExceptionalSelbergMainConstant_pos



/-! ## The finite Selberg output and its normalized remainder -/







/-- The integer quotient length of the upper physical interval costs at
most its real length plus one. -/
theorem paperExceptionalQuotientLength_cast_le
    {n h b : ℕ} (hb : 0 < b) :
    ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ)) ≤
      (h : ℝ) / (b : ℝ) + 1 := by
  have habs := quotientIocLength_sub_realLengthDiv_abs_lt_one
    (D := b) (lo := 2 * n) (hi := 2 * n + h) hb (by omega)
  have hright := (abs_lt.mp habs).2
  have hsub : 2 * n + h - 2 * n = h := by omega
  rw [hsub] at hright
  linarith



/-! ## The endpoint remainder tends to zero -/





/-! ## Uniform packaging of the finite majorant -/



/-- The harmless `1+log(2X)` in the finite harmonic sum is eventually
absorbed by a second copy of `deltaStar*L`. -/
theorem eventually_one_add_log_two_mul_exceptionalCutoff_le
    {deltaStar : ℝ} (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      1 + Real.log
          ((2 * tangentPaperExceptionalCutoff deltaStar n : ℕ) : ℝ) ≤
        2 * deltaStar * L n := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hLTop.eventually
    (eventually_ge_atTop
      ((1 + 2 * Real.log 2) / deltaStar))
  filter_upwards [eventually_ge_atTop 1, hlarge] with n hn hLn
  have hcutPosNat :
      0 < tangentPaperExceptionalCutoff deltaStar n :=
    tangentPaperExceptionalCutoff_pos hdelta.le hn
  have hcutPos :
      (0 : ℝ) < tangentPaperExceptionalCutoff deltaStar n := by
    exact_mod_cast hcutPosNat
  have hcutLog := tangentPaperExceptionalCutoff_log_le
    hdelta.le hn
  have hdeltaDominates :
      1 + 2 * Real.log 2 ≤ deltaStar * L n := by
    have h := (div_le_iff₀ hdelta).mp hLn
    simpa only [mul_comm] using h
  have hlogProduct :
      Real.log
          ((2 * tangentPaperExceptionalCutoff deltaStar n : ℕ) : ℝ) =
        Real.log 2 +
          Real.log (tangentPaperExceptionalCutoff deltaStar n : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hcutPos.ne']
  rw [hlogProduct]
  nlinarith





/-! ## Exact support cutoff for the actual fixed charge -/

/-- A literal exceptional upper factor has smooth part strictly below twice
the paper's real cutoff `n^deltaStar`, once the paper tail lies below `n`.
This is the exact support statement used in the paper's assertion that the
exceptional charge vanishes for `p > 2*n^deltaStar`. -/
theorem completeSmoothPart_cast_lt_two_mul_realExceptionalCutoff
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h a : ℕ} (hn : 1 ≤ n) (hh : h ≤ n)
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    (completeSmoothPart (yNat n) a : ℝ) <
      2 * (n : ℝ) ^ deltaStar := by
  have haData := mem_paperExceptionalUpperFactors.mp ha
  have haBounds : 2 * n < a ∧ a ≤ 2 * n + h := by
    simpa only [roughUpperBlock, Finset.mem_Ioc] using haData.1
  have haUpper : a ≤ 3 * n := by omega
  let rough := completeRoughLabel (yNat n) a
  let smooth := completeSmoothPart (yNat n) a
  have hroughPos : 0 < rough := completeRoughLabel_pos (yNat n) a
  have hroughR : (0 : ℝ) < rough := by exact_mod_cast hroughPos
  have hsmoothLe : (smooth : ℝ) ≤ (a : ℝ) / (rough : ℝ) := by
    exact Nat.cast_div_le
  have haUpperR : (a : ℝ) ≤ 3 * (n : ℝ) := by
    exact_mod_cast haUpper
  have haDiv : (a : ℝ) / (rough : ℝ) ≤
      3 * (n : ℝ) / (rough : ℝ) :=
    div_le_div_of_nonneg_right haUpperR hroughR.le
  have hexceptional :
      2 * (n : ℝ) / (rough : ℝ) <
        (n : ℝ) ^ deltaStar := by
    simpa only [rough] using haData.2
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast hn) hdeltaNonneg
  have hthree :
      3 * (n : ℝ) / (rough : ℝ) =
        (3 / 2 : ℝ) *
          (2 * (n : ℝ) / (rough : ℝ)) := by ring
  have hthreePower :
      3 * (n : ℝ) / (rough : ℝ) <
        2 * (n : ℝ) ^ deltaStar := by
    rw [hthree]
    nlinarith
  exact hsmoothLe.trans_lt (haDiv.trans_lt hthreePower)

/-- Safe integral-cutoff corollary of the literal real support bound. -/
theorem completeSmoothPart_lt_two_mul_exceptionalCutoff
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h a : ℕ} (hn : 1 ≤ n) (hh : h ≤ n)
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    completeSmoothPart (yNat n) a <
      2 * tangentPaperExceptionalCutoff deltaStar n := by
  have hsmoothReal :=
    completeSmoothPart_cast_lt_two_mul_realExceptionalCutoff
      hdeltaNonneg hn hh ha
  have hcut := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  have hsmoothCast : (completeSmoothPart (yNat n) a : ℝ) <
      2 * (tangentPaperExceptionalCutoff deltaStar n : ℝ) :=
    hsmoothReal.trans_le
      (mul_le_mul_of_nonneg_left hcut (by norm_num))
  exact_mod_cast hsmoothCast

/-- Every smooth part which actually occurs is contained in the positive
prefix used by the valuation-sum lemmas. -/
theorem paperExceptionalSmoothParts_subset_Icc_two_mul_cutoff
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h : ℕ} (hn : 1 ≤ n) (hh : h ≤ n) :
    paperExceptionalSmoothParts n h deltaStar ⊆
      Finset.Icc 1 (2 * tangentPaperExceptionalCutoff deltaStar n) := by
  intro b hb
  obtain ⟨a, haExceptional, hab⟩ :=
    mem_paperExceptionalSmoothParts.mp hb
  have haPos : 0 < a := paperExceptionalUpperFactors_pos haExceptional
  have hbPos : 0 < b := by
    simpa only [hab] using completeSmoothPart_pos
      (y := yNat n) (a := a) haPos
  have hbLt : b < 2 * tangentPaperExceptionalCutoff deltaStar n := by
    simpa only [hab] using
      completeSmoothPart_lt_two_mul_exceptionalCutoff
        hdeltaNonneg hn hh haExceptional
  exact Finset.mem_Icc.mpr ⟨hbPos, hbLt.le⟩

/-! ## Closing the finite weighted Selberg estimate -/

/-- The actual low-prime valuation of `G_fix` is eventually bounded by the
canonical finite majorant.  This theorem is the composition of the literal
smooth-fibre decomposition, the canonical Lambda-squared interval sieve,
and the elementary valuation prefix estimates; it has no charge-bound
premise. -/
theorem eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) (p : ℕ),
        p.Prime → p ≤ yNat n →
        (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
            ℝ) ≤
          paperExceptionalFiniteChargeMajorant c deltaStar n p := by
  filter_upwards
    [eventually_ge_atTop 3,
      eventually_upperTailLength_le hc,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      eventually_one_add_log_two_mul_exceptionalCutoff_le hdelta,
      eventually_paperExceptionalSmoothFiber_card_le_canonicalLambdaSquare]
      with n hn htail hlogY hcutLog hfiber
  intro R p hpPrime hpLow
  let h := upperTailLength c n
  let X := tangentPaperExceptionalCutoff deltaStar n
  let Y := yNat n
  let smoothParts := paperExceptionalSmoothParts n h deltaStar
  have hnOne : 1 ≤ n := by omega
  have hpPos : 0 < p := hpPrime.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPos
  have hL : 0 < L n := L_pos (by omega)
  have hlogYPos : 0 < Real.log (Y : ℝ) := by
    exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL).trans_le
      (by simpa only [Y] using hlogY)
  have hYOne : (1 : ℝ) ≤ Y := by
    have hYgt : (1 : ℝ) < Y :=
      (Real.log_pos_iff (Nat.cast_nonneg Y)).mp hlogYPos
    exact hYgt.le
  have hlogYLeY : Real.log (Y : ℝ) ≤ (Y : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Y)
    linarith
  have hYLeFour : (Y : ℝ) ≤ (Y : ℝ) ^ 4 := by
    have hcube : (1 : ℝ) ≤ (Y : ℝ) ^ 3 :=
      one_le_pow₀ hYOne
    calc
      (Y : ℝ) = (Y : ℝ) * 1 := by ring
      _ ≤ (Y : ℝ) * (Y : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (Nat.cast_nonneg Y)
      _ = (Y : ℝ) ^ 4 := by ring
  have hlogYLeFour :
      Real.log (Y : ℝ) ≤ (Y : ℝ) ^ 4 :=
    hlogYLeY.trans hYLeFour
  have hXPos : 0 < X := by
    exact tangentPaperExceptionalCutoff_pos hdelta.le hnOne
  have hBOne : 1 ≤ 2 * X := by omega
  have hsmoothSubset : smoothParts ⊆ Finset.Icc 1 (2 * X) := by
    simpa only [smoothParts, h, X] using
      paperExceptionalSmoothParts_subset_Icc_two_mul_cutoff
        hdelta.le hnOne htail
  have hchargeNat :=
    R.paperFixedExceptionalFactors_prod_factorization_le_smoothFiberSum
      (deltaStar := deltaStar) hpLow
  have hchargeCast :
      (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
          ℝ) ≤
        ((∑ b ∈ smoothParts,
            b.factorization p *
              (paperExceptionalSmoothFiber n h deltaStar b).card : ℕ) :
          ℝ) := by
    dsimp only [smoothParts, h]
    exact_mod_cast hchargeNat
  have hcharge :
      (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
          ℝ) ≤
        ∑ b ∈ smoothParts,
          (b.factorization p : ℝ) *
            ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) := by
    calc
      (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
          ℝ) ≤
        ((∑ b ∈ smoothParts,
            b.factorization p *
              (paperExceptionalSmoothFiber n h deltaStar b).card : ℕ) :
          ℝ) := hchargeCast
      _ = ∑ b ∈ smoothParts,
          (b.factorization p : ℝ) *
            ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) := by
        push_cast
        rfl
  have hrest :
      paperExceptionalSelbergMainConstant / Real.log (Y : ℝ) +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2 ≤
        paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
          Real.log (Y : ℝ) ^ 2 := by
    have hmainRest :
        paperExceptionalSelbergMainConstant / Real.log (Y : ℝ) ≤
          paperExceptionalSelbergMainConstant * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2 := by
      calc
        paperExceptionalSelbergMainConstant / Real.log (Y : ℝ) =
            paperExceptionalSelbergMainConstant * Real.log (Y : ℝ) /
              Real.log (Y : ℝ) ^ 2 := by
          field_simp [hlogYPos.ne']
        _ ≤ paperExceptionalSelbergMainConstant * (Y : ℝ) ^ 4 /
              Real.log (Y : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogYLeFour
              paperExceptionalSelbergMainConstant_pos.le)
            (sq_nonneg _)
    calc
      paperExceptionalSelbergMainConstant / Real.log (Y : ℝ) +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2 ≤
        paperExceptionalSelbergMainConstant * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2 +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2 :=
      add_le_add_left hmainRest _
      _ = paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
          Real.log (Y : ℝ) ^ 2 := by
        unfold paperExceptionalSelbergRemainderConstant
        unfold paperExceptionalSelbergMainConstant
        ring
  have hpointwise : ∀ b ∈ smoothParts,
      (b.factorization p : ℝ) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
        ((h : ℝ) * paperExceptionalSelbergMainConstant /
            Real.log (Y : ℝ)) *
            ((b.factorization p : ℝ) / (b : ℝ)) +
          (paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2) *
            (b.factorization p : ℝ) := by
    intro b hb
    have hbIcc := Finset.mem_Icc.mp (hsmoothSubset hb)
    have hbPos : 0 < b := by omega
    have hbR : (0 : ℝ) < b := by exact_mod_cast hbPos
    have hfiberB := hfiber h b deltaStar
    have hlength := paperExceptionalQuotientLength_cast_le
      (n := n) (h := h) hbPos
    have hcard :
        ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
          (h : ℝ) * paperExceptionalSelbergMainConstant /
              (Real.log (Y : ℝ) * (b : ℝ)) +
            paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
              Real.log (Y : ℝ) ^ 2 := by
      calc
        ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
            ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ) *
                (tangentSelbergCanonicalMainConstant /
                  Real.log (Y : ℝ)) +
              tangentSelbergCanonicalLambdaConstant ^ 2 *
                  (Y : ℝ) ^ 4 / Real.log (Y : ℝ) ^ 2) := by
          simpa only [Y] using hfiberB
        _ ≤ ((h : ℝ) / (b : ℝ) + 1) *
                (paperExceptionalSelbergMainConstant /
                  Real.log (Y : ℝ)) +
              tangentSelbergCanonicalLambdaConstant ^ 2 *
                  (Y : ℝ) ^ 4 / Real.log (Y : ℝ) ^ 2 := by
          apply add_le_add_left
          exact mul_le_mul_of_nonneg_right hlength
            (div_nonneg paperExceptionalSelbergMainConstant_pos.le
              hlogYPos.le)
        _ = (h : ℝ) * paperExceptionalSelbergMainConstant /
                (Real.log (Y : ℝ) * (b : ℝ)) +
              (paperExceptionalSelbergMainConstant /
                  Real.log (Y : ℝ) +
                tangentSelbergCanonicalLambdaConstant ^ 2 *
                  (Y : ℝ) ^ 4 / Real.log (Y : ℝ) ^ 2) := by
          field_simp [hbR.ne', hlogYPos.ne']
          ; ring
        _ ≤ (h : ℝ) * paperExceptionalSelbergMainConstant /
                (Real.log (Y : ℝ) * (b : ℝ)) +
              paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
                Real.log (Y : ℝ) ^ 2 := add_le_add_right hrest _
    have hmul := mul_le_mul_of_nonneg_left hcard
      (Nat.cast_nonneg (b.factorization p))
    calc
      (b.factorization p : ℝ) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
        (b.factorization p : ℝ) *
          ((h : ℝ) * paperExceptionalSelbergMainConstant /
              (Real.log (Y : ℝ) * (b : ℝ)) +
            paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
              Real.log (Y : ℝ) ^ 2) := hmul
      _ = ((h : ℝ) * paperExceptionalSelbergMainConstant /
              Real.log (Y : ℝ)) *
            ((b.factorization p : ℝ) / (b : ℝ)) +
          (paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
              Real.log (Y : ℝ) ^ 2) *
            (b.factorization p : ℝ) := by
        field_simp [hbR.ne', hlogYPos.ne']
  have hweightedSubset :
      (∑ b ∈ smoothParts,
          (b.factorization p : ℝ) / (b : ℝ)) ≤
        ∑ b ∈ Finset.Icc 1 (2 * X),
          (b.factorization p : ℝ) / (b : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsmoothSubset
      (fun _b _hbIcc _hbSmooth ↦ by positivity)
  have hunweightedSubset :
      (∑ b ∈ smoothParts, (b.factorization p : ℝ)) ≤
        ∑ b ∈ Finset.Icc 1 (2 * X),
          (b.factorization p : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsmoothSubset
      (fun _b _hbIcc _hbSmooth ↦ Nat.cast_nonneg _)
  have hweightedFull :=
    weightedFactorizationSum_le_two_mul_one_add_log_div_prime
      (p := p) (B := 2 * X) hpPrime hBOne
  have hunweightedFull :=
    sum_factorization_Icc_cast_le_two_mul_div_prime
      (p := p) (B := 2 * X) hpPrime
  have hweighted :
      (∑ b ∈ smoothParts,
          (b.factorization p : ℝ) / (b : ℝ)) ≤
        4 * deltaStar * L n / (p : ℝ) := by
    calc
      (∑ b ∈ smoothParts,
          (b.factorization p : ℝ) / (b : ℝ)) ≤
        ∑ b ∈ Finset.Icc 1 (2 * X),
          (b.factorization p : ℝ) / (b : ℝ) := hweightedSubset
      _ ≤ 2 * (1 + Real.log ((2 * X : ℕ) : ℝ)) /
          (p : ℝ) := hweightedFull
      _ ≤ 4 * deltaStar * L n / (p : ℝ) := by
        apply div_le_div_of_nonneg_right _ hpR.le
        have hcutLog' :
            1 + Real.log ((2 * X : ℕ) : ℝ) ≤
              2 * deltaStar * L n := by
          simpa only [X] using hcutLog
        nlinarith
  have hunweighted :
      (∑ b ∈ smoothParts, (b.factorization p : ℝ)) ≤
        4 * (X : ℝ) / (p : ℝ) := by
    calc
      (∑ b ∈ smoothParts, (b.factorization p : ℝ)) ≤
          ∑ b ∈ Finset.Icc 1 (2 * X),
            (b.factorization p : ℝ) := hunweightedSubset
      _ ≤ 2 * ((2 * X : ℕ) : ℝ) / (p : ℝ) :=
        hunweightedFull
      _ = 4 * (X : ℝ) / (p : ℝ) := by push_cast; ring
  have hmainCoefficient : 0 ≤
      (h : ℝ) * paperExceptionalSelbergMainConstant /
        Real.log (Y : ℝ) := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        paperExceptionalSelbergMainConstant_pos.le)
      hlogYPos.le
  have hrestCoefficient : 0 ≤
      paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
        Real.log (Y : ℝ) ^ 2 := by
    exact div_nonneg
      (mul_nonneg paperExceptionalSelbergRemainderConstant_pos.le
        (by positivity))
      (sq_nonneg _)
  calc
    (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
        ℝ) ≤
      ∑ b ∈ smoothParts,
        (b.factorization p : ℝ) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) := hcharge
    _ ≤ ∑ b ∈ smoothParts,
        (((h : ℝ) * paperExceptionalSelbergMainConstant /
            Real.log (Y : ℝ)) *
            ((b.factorization p : ℝ) / (b : ℝ)) +
          (paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2) *
            (b.factorization p : ℝ)) :=
      Finset.sum_le_sum hpointwise
    _ = ((h : ℝ) * paperExceptionalSelbergMainConstant /
          Real.log (Y : ℝ)) *
          (∑ b ∈ smoothParts,
            (b.factorization p : ℝ) / (b : ℝ)) +
        (paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
          Real.log (Y : ℝ) ^ 2) *
          (∑ b ∈ smoothParts, (b.factorization p : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ((h : ℝ) * paperExceptionalSelbergMainConstant /
          Real.log (Y : ℝ)) *
          (4 * deltaStar * L n / (p : ℝ)) +
        (paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
          Real.log (Y : ℝ) ^ 2) *
          (4 * (X : ℝ) / (p : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hweighted hmainCoefficient)
        (mul_le_mul_of_nonneg_left hunweighted hrestCoefficient)
    _ = paperExceptionalFiniteChargeMajorant c deltaStar n p := by
      unfold paperExceptionalFiniteChargeMajorant
      simp only [h, X, Y, paperExceptionalSelbergMainConstant]
      ring











end

end Erdos390.WholePaper

end

theorem solution :
∀ {c deltaStar : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      ∀ᶠ (n : Nat) in Filter.atTop.{0},
        ∀
          (R :
            Erdos390.WholePaper.BankPaperRealization n
              (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
          (p : Nat),
          Nat.Prime p →
            LE.le.{0} p (Erdos390.Full.ArithmeticModel.yNat n) →
              LE.le.{0}
                (↑((Nat.factorization
                      (Finset.prod.{0, 0}
                        (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar) id.{1}))
                    p))
                (Erdos390.WholePaper.paperExceptionalFiniteChargeMajorant c deltaStar n p) := by
  exact @Erdos390.WholePaper.eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant
