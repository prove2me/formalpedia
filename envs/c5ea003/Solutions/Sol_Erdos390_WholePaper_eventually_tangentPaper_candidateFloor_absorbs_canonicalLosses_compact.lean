-- Prove2me | solution 1 for Erdos390.WholePaper.eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:52:19.577609+00:00
-- url     : https://prove2.me/submissions/9ec676d6-7e09-4ad0-ac88-f82174e29307

import Definitions.Def_erdos390_remaining_analytic_propositions_008
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
import Theorems.Thm_Erdos390_WholePaper_eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap
import Theorems.Thm_Erdos390_WholePaper_eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap
import Theorems.Thm_Erdos390_WholePaper_tangentRoughHeadCandidateMain_normalized_ge_three_quarters_compact


section
theorem Erdos390.WholePaper.tangentRoughHeadCandidateMain_normalized_ge_three_quarters : Erdos390.RemainingAnalyticGoal008_040 := @Erdos390.WholePaper.tangentRoughHeadCandidateMain_normalized_ge_three_quarters_compact
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

/- Source module: Erdos390.WholePaper.SafePrimeCounting -/
section


/-!
# A prime-counting asymptotic with an audited dependency closure

The pinned auxiliary package contains stronger convenience theorems whose
transitive imports include unfinished declarations.  This file instead
derives `π(x) ~ x / log x` from the already audited `MediumPNT` route used by
`FriableAsymptotic.theta_error_isBigO_log_power` and Mathlib's elementary
comparison between `π` and `θ`.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

private theorem div_log_isLittleO_id :
    (fun x : ℝ => x / Real.log x) =o[atTop] (fun x : ℝ => x) := by
  apply (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr
  apply Real.tendsto_log_atTop.inv_tendsto_atTop.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  exact inv_mul_cancel₀ hlog

private theorem div_log_sq_isLittleO_div_log :
    (fun x : ℝ => x / Real.log x ^ 2) =o[atTop]
      (fun x : ℝ => x / Real.log x) := by
  apply (isLittleO_iff_tendsto (fun x hx => by
    apply div_eq_zero_iff.mpr
    rcases (div_eq_zero_iff.mp hx) with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by simp [hx]))).mpr
  apply Real.tendsto_log_atTop.inv_tendsto_atTop.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  exact inv_mul_cancel₀ hlog

theorem theta_sub_id_isLittleO :
    (Chebyshev.theta - id) =o[atTop] (id : ℝ → ℝ) := by
  have htheta :
      (Chebyshev.theta - id) =O[atTop]
        (fun x : ℝ => x / Real.log x) := by
    simpa using
      Erdos390.Full.FriableAsymptotic.theta_error_isBigO_log_power 1
  exact htheta.trans_isLittleO div_log_isLittleO_id

theorem theta_div_log_sub_main_isLittleO :
    (fun x : ℝ =>
      Chebyshev.theta x / Real.log x - x / Real.log x) =o[atTop]
        (fun x : ℝ => x / Real.log x) := by
  have hmul := theta_sub_id_isLittleO.mul_isBigO
    (isBigO_refl (fun x : ℝ => (Real.log x)⁻¹) atTop)
  apply hmul.congr'
  · exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, id_eq]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
  · exact Eventually.of_forall fun x => by
      simp only [id_eq]
      rw [div_eq_mul_inv]

theorem primeCounting_sub_main_isLittleO :
    (fun x : ℝ =>
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =o[atTop]
        (fun x : ℝ => x / Real.log x) := by
  have hpi :
      (fun x : ℝ =>
        (Nat.primeCounting ⌊x⌋₊ : ℝ) -
          Chebyshev.theta x / Real.log x) =o[atTop]
          (fun x : ℝ => x / Real.log x) :=
    Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO
      div_log_sq_isLittleO_div_log
  have hadd := hpi.add theta_div_log_sub_main_isLittleO
  apply hadd.congr' (Eventually.of_forall fun x => by ring) (Eventually.of_forall fun _ => rfl)

/-- Safe real-variable prime number theorem. -/
theorem primeCounting_real_isEquivalent :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x : ℝ => x / Real.log x) :=
  primeCounting_sub_main_isLittleO

/-- Safe natural-variable form used to count the thirteen layers. -/
theorem primeCounting_nat_isEquivalent :
    (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  have h := primeCounting_real_isEquivalent.comp_tendsto
    tendsto_natCast_atTop_atTop
  refine (h.congr_left ?_).congr_right ?_
  · exact Eventually.of_forall fun n => by
      simp [Function.comp_apply, Nat.floor_natCast]
  · exact Eventually.of_forall fun n => by
      rfl

end Erdos390.WholePaper.SafePrimeCounting

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

/- Source module: Erdos390.WholePaper.BankBottomConcreteDemand -/
section


/-!
# Concrete request demand for the eight bottom bank pools

The formal floating-rounding theorem produces the sharper floor-log error box
`4 * log_2(M) * log_p(M)`.  We reserve the paper's ceiling-log,
endpoint-free box at `3n`.  A request is an actual signed bank
slot together with one of the four bottom moves; its sign selects the fixed
orientation pool.  Thus every one of the eight pool fibers has exactly
`sum_{p <= floor(n^(2/9))} beta_p` requests.

The analytic count is also proved here.  Primes below `(3n)^(1/5)` are
bounded trivially; their contribution is `o(n^(2/9))`.  Above that cutoff,
`clog_p(3n) <= 5`, while the safe PNT gives `pi(y) = O(y / log y)`.  Since
`log y` is a fixed positive fraction of `log n`, the total demand is
`O(y)`, hence negligible compared with `n / (log n)^2`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section





































private theorem bankRoundingBeta_le_head
    {n p : ℕ} (hp : p.Prime) :
    bankRoundingBeta n p ≤
      4 * bankRoundingDepth n * bankRoundingDepth n := by
  have hclog : Nat.clog p (3 * n) ≤ Nat.clog 2 (3 * n) :=
    Nat.clog_anti_left Nat.one_lt_two hp.two_le
  rw [bankRoundingBeta, bankRoundingDepth]
  exact Nat.mul_le_mul_left (4 * Nat.clog 2 (3 * n)) hclog

private theorem bankRoundingBeta_le_tail
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hcut : bankRoundingHeadCutoff n < p) :
    bankRoundingBeta n p ≤ 20 * bankRoundingDepth n := by
  let root : ℝ := (3 * (n : ℝ)) ^ (1 / 5 : ℝ)
  have hrootPos : 0 < root := by
    dsimp [root]
    positivity
  have hrootLt : root < (p : ℝ) := by
    have hfloor : root < (bankRoundingHeadCutoff n : ℝ) + 1 := by
      simpa only [root, bankRoundingHeadCutoff] using
        (Nat.lt_floor_add_one root)
    have hsucc : bankRoundingHeadCutoff n + 1 ≤ p := by omega
    have hsuccR : (bankRoundingHeadCutoff n : ℝ) + 1 ≤ (p : ℝ) := by
      exact_mod_cast hsucc
    exact hfloor.trans_le hsuccR
  have hrootPow : root ^ (5 : ℕ) = 3 * (n : ℝ) := by
    dsimp [root]
    calc
      ((3 * (n : ℝ)) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) =
          (3 * (n : ℝ)) ^ ((1 / 5 : ℝ) * (5 : ℕ)) :=
        (Real.rpow_mul_natCast (by positivity) _ _).symm
      _ = 3 * (n : ℝ) := by norm_num [Real.rpow_one]
  have hpowR : 3 * (n : ℝ) < (p : ℝ) ^ (5 : ℕ) := by
    rw [← hrootPow]
    exact pow_lt_pow_left₀ hrootLt hrootPos.le (by omega)
  have hpow : 3 * n < p ^ 5 := by exact_mod_cast hpowR
  have hclog : Nat.clog p (3 * n) ≤ 5 :=
    (Nat.clog_le_iff_le_pow hp.one_lt).2 hpow.le
  calc
    bankRoundingBeta n p =
        4 * bankRoundingDepth n * Nat.clog p (3 * n) := rfl
    _ ≤ 4 * bankRoundingDepth n * 5 :=
      Nat.mul_le_mul_left _ hclog
    _ = 20 * bankRoundingDepth n := by ring

/-- Exact finite beta-sum estimate underlying the asymptotic demand bound. -/
theorem bankBottomPaperDemand_le_majorant (n : ℕ) :
    bankBottomPaperDemand n ≤ bankBottomPaperDemandMajorant n := by
  classical
  let P := bankRoundingPrimeSupport n
  let head := P.filter (fun p ↦ p ≤ bankRoundingHeadCutoff n)
  let tail := P.filter (fun p ↦ ¬p ≤ bankRoundingHeadCutoff n)
  have hsplit :
      (∑ p ∈ P, bankRoundingBeta n p) =
        (∑ p ∈ head, bankRoundingBeta n p) +
          ∑ p ∈ tail, bankRoundingBeta n p := by
    simpa only [head, tail] using
      (P.sum_filter_add_sum_filter_not
        (fun p ↦ p ≤ bankRoundingHeadCutoff n)
        (fun p ↦ bankRoundingBeta n p)).symm
  have hheadPoint : ∀ p ∈ head,
      bankRoundingBeta n p ≤
        4 * bankRoundingDepth n * bankRoundingDepth n := by
    intro p hp
    exact bankRoundingBeta_le_head
      (bankRoundingPrimeSupport_prime (Finset.mem_filter.mp hp).1)
  have hheadCard : head.card ≤ bankRoundingHeadCutoff n + 1 := by
    have hsubset : head ⊆ Finset.range (bankRoundingHeadCutoff n + 1) := by
      intro p hp
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
    simpa using Finset.card_le_card hsubset
  have hhead :
      (∑ p ∈ head, bankRoundingBeta n p) ≤
        (bankRoundingHeadCutoff n + 1) *
          (4 * bankRoundingDepth n * bankRoundingDepth n) := by
    calc
      (∑ p ∈ head, bankRoundingBeta n p) ≤
          head.card *
            (4 * bankRoundingDepth n * bankRoundingDepth n) := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul head (fun p ↦ bankRoundingBeta n p)
            (4 * bankRoundingDepth n * bankRoundingDepth n) hheadPoint
      _ ≤ (bankRoundingHeadCutoff n + 1) *
          (4 * bankRoundingDepth n * bankRoundingDepth n) :=
        Nat.mul_le_mul_right _ hheadCard
  have htailPoint : ∀ p ∈ tail,
      bankRoundingBeta n p ≤ 20 * bankRoundingDepth n := by
    intro p hp
    by_cases hn : n = 0
    · subst n
      simp [bankRoundingBeta, bankRoundingDepth]
    · apply bankRoundingBeta_le_tail (Nat.pos_of_ne_zero hn)
        (bankRoundingPrimeSupport_prime (Finset.mem_filter.mp hp).1)
      exact Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
  have hPcard : P.card = Nat.primeCounting (yNat n) := by
    simpa only [P, bankRoundingPrimeSupport, Nat.primeCounting] using
      Nat.primesBelow_card_eq_primeCounting' (yNat n + 1)
  have htailCard : tail.card ≤ Nat.primeCounting (yNat n) := by
    rw [← hPcard]
    exact Finset.card_filter_le _ _
  have htail :
      (∑ p ∈ tail, bankRoundingBeta n p) ≤
        Nat.primeCounting (yNat n) * (20 * bankRoundingDepth n) := by
    calc
      (∑ p ∈ tail, bankRoundingBeta n p) ≤
          tail.card * (20 * bankRoundingDepth n) := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul tail (fun p ↦ bankRoundingBeta n p)
            (20 * bankRoundingDepth n) htailPoint
      _ ≤ Nat.primeCounting (yNat n) *
          (20 * bankRoundingDepth n) :=
        Nat.mul_le_mul_right _ htailCard
  rw [bankBottomPaperDemand, bankBottomPaperDemandMajorant]
  change (∑ p ∈ P, bankRoundingBeta n p) ≤ _
  rw [hsplit]
  calc
    (∑ p ∈ head, bankRoundingBeta n p) +
        ∑ p ∈ tail, bankRoundingBeta n p ≤
      (bankRoundingHeadCutoff n + 1) *
          (4 * bankRoundingDepth n * bankRoundingDepth n) +
        Nat.primeCounting (yNat n) *
          (20 * bankRoundingDepth n) := Nat.add_le_add hhead htail
    _ = 4 * bankRoundingDepth n * bankRoundingDepth n *
          (bankRoundingHeadCutoff n + 1) +
        20 * bankRoundingDepth n * Nat.primeCounting (yNat n) := by ring

private theorem yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

private theorem eventually_y_half_le_yNat :
    ∀ᶠ n : ℕ in atTop, y n / 2 ≤ (yNat n : ℝ) := by
  have hyTop : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  filter_upwards [hyTop.eventually (eventually_ge_atTop (2 : ℝ))] with n hyn
  have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
  linarith

private theorem bankRoundingDepth_le_two_mul_log2
    {n : ℕ} (hn : 0 < n) :
    bankRoundingDepth n ≤ 2 * Nat.log2 (3 * n) := by
  have hX : 3 * n ≠ 0 := by omega
  have hone : 1 ≤ Nat.log 2 (3 * n) :=
    (Nat.le_log_iff_pow_le Nat.one_lt_two hX).2 (by
      simpa only [pow_one] using (show 2 ≤ 3 * n by omega))
  have hceil : Nat.clog 2 (3 * n) ≤ (Nat.log 2 (3 * n)).succ :=
    Nat.clog_le_of_le_pow
      (Nat.lt_pow_succ_log_self Nat.one_lt_two (3 * n)).le
  rw [bankRoundingDepth, Nat.log2_eq_log_two]
  omega

private theorem bankRoundingDepth_cast_le_two_logb
    {n : ℕ} (hn : 0 < n) :
    (bankRoundingDepth n : ℝ) ≤
      2 * (Real.log (3 * (n : ℝ)) / Real.log 2) := by
  have hnat := bankRoundingDepth_le_two_mul_log2 hn
  have hcast : (bankRoundingDepth n : ℝ) ≤
      2 * (Nat.log2 (3 * n) : ℝ) := by exact_mod_cast hnat
  have hfloor : (Nat.log2 (3 * n) : ℝ) ≤
      Real.logb 2 ((3 * n : ℕ) : ℝ) := Real.log2_le_logb (3 * n)
  calc
    (bankRoundingDepth n : ℝ) ≤ 2 * (Nat.log2 (3 * n) : ℝ) := hcast
    _ ≤ 2 * Real.logb 2 ((3 * n : ℕ) : ℝ) := by gcongr
    _ = 2 * (Real.log (3 * (n : ℝ)) / Real.log 2) := by
      norm_num [Real.logb]



private theorem bankRoundingDepth_isBigO_log_yNat :
    (fun n : ℕ ↦ (bankRoundingDepth n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (yNat n : ℝ)) := by
  apply IsBigO.of_bound (20 / Real.log 2)
  filter_upwards [eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
      with n hn hyLog
  have hnPos : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogY : 0 < Real.log (yNat n : ℝ) := by
    have : 0 < (1 / 5 : ℝ) * L n := mul_pos (by norm_num) (by simpa [L])
    exact this.trans_le hyLog
  have hlogThree : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogMul : Real.log (3 * (n : ℝ)) =
      Real.log 3 + Real.log (n : ℝ) :=
    Real.log_mul (by norm_num) hnPos.ne'
  have hdepth := bankRoundingDepth_cast_le_two_logb
    (show 0 < n by omega)
  rw [hlogMul] at hdepth
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLn : L n ≤ 5 * Real.log (yNat n : ℝ) := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ bankRoundingDepth n),
    Real.norm_eq_abs, abs_of_nonneg hlogY.le]
  have hsum : Real.log 3 + Real.log (n : ℝ) ≤
      2 * Real.log (n : ℝ) := by linarith
  have hbase : (bankRoundingDepth n : ℝ) ≤
      (4 / Real.log 2) * L n := by
    calc
      (bankRoundingDepth n : ℝ) ≤
          2 * ((Real.log 3 + Real.log (n : ℝ)) / Real.log 2) := hdepth
      _ ≤ 2 * ((2 * Real.log (n : ℝ)) / Real.log 2) := by
        exact mul_le_mul_of_nonneg_left
          ((div_le_div_iff_of_pos_right hlogTwo).2 hsum) (by norm_num)
      _ = (4 / Real.log 2) * L n := by
        rw [L]
        ring
  calc
    (bankRoundingDepth n : ℝ) ≤
        (4 / Real.log 2) * L n := hbase
    _ ≤ (4 / Real.log 2) * (5 * Real.log (yNat n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLn (by positivity)
    _ = (20 / Real.log 2) * Real.log (yNat n : ℝ) := by ring

private theorem bankRoundingHeadMajorant_isLittleO_yNat :
    (fun n : ℕ ↦
      ((4 * bankRoundingDepth n * bankRoundingDepth n *
        (bankRoundingHeadCutoff n + 1) : ℕ) : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ)) := by
  let headModel : ℕ → ℝ := fun n ↦
    (3 * (n : ℝ)) ^ (1 / 5 : ℝ) * Real.log (3 * (n : ℝ)) ^ 2
  have hheadO :
      (fun n : ℕ ↦
        ((4 * bankRoundingDepth n * bankRoundingDepth n *
          (bankRoundingHeadCutoff n + 1) : ℕ) : ℝ)) =O[atTop]
        headModel := by
    apply IsBigO.of_bound (32 / Real.log 2 ^ 2)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hroot : 1 ≤ (3 * (n : ℝ)) ^ (1 / 5 : ℝ) :=
      Real.one_le_rpow
        (by exact_mod_cast (show 1 ≤ 3 * n by omega)) (by norm_num)
    have hcutCast : (bankRoundingHeadCutoff n : ℝ) ≤
        (3 * (n : ℝ)) ^ (1 / 5 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have hcut : (bankRoundingHeadCutoff n : ℝ) + 1 ≤
        2 * (3 * (n : ℝ)) ^ (1 / 5 : ℝ) := by linarith
    have hdepth := bankRoundingDepth_cast_le_two_logb hn
    have hlogNonneg : 0 ≤ Real.log (3 * (n : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * n by omega))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (4 * bankRoundingDepth n * bankRoundingDepth n *
          (bankRoundingHeadCutoff n + 1) : ℕ)),
      Real.norm_eq_abs, abs_of_nonneg (by
        exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))]
    push_cast
    calc
      (4 : ℝ) * bankRoundingDepth n * bankRoundingDepth n *
          ((bankRoundingHeadCutoff n : ℝ) + 1) ≤
        4 * (2 * (Real.log (3 * (n : ℝ)) / Real.log 2)) *
          (2 * (Real.log (3 * (n : ℝ)) / Real.log 2)) *
            (2 * (3 * (n : ℝ)) ^ (1 / 5 : ℝ)) := by gcongr
      _ = (32 / Real.log 2 ^ 2) * headModel n := by
        dsimp [headModel]
        ring
  have hreal0 :
      (fun x : ℝ ↦ Real.log x ^ (2 : ℕ) * x ^ (1 / 5 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ x ^ (1 / 45 : ℝ) * x ^ (1 / 5 : ℝ)) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2
        (by norm_num : (0 : ℝ) < 1 / 45)).mul_isBigO
          (isBigO_refl (fun x : ℝ ↦ x ^ (1 / 5 : ℝ)) atTop)
  have hreal :
      (fun x : ℝ ↦ x ^ (1 / 5 : ℝ) * Real.log x ^ 2) =o[atTop]
        (fun x : ℝ ↦ x ^ (2 / 9 : ℝ)) := by
    apply hreal0.congr'
    · exact Eventually.of_forall fun x ↦ by
        change Real.log x ^ (2 : ℕ) * x ^ (1 / 5 : ℝ) =
          x ^ (1 / 5 : ℝ) * Real.log x ^ (2 : ℕ)
        exact mul_comm (Real.log x ^ (2 : ℕ)) (x ^ (1 / 5 : ℝ))
    · filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_add hx]
      norm_num
  have hthreeTop : Tendsto (fun n : ℕ ↦ 3 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hmodel : headModel =o[atTop]
      (fun n : ℕ ↦ (3 * (n : ℝ)) ^ (2 / 9 : ℝ)) := by
    simpa only [headModel] using hreal.comp_tendsto hthreeTop
  have hscaledY :
      (fun n : ℕ ↦ (3 * (n : ℝ)) ^ (2 / 9 : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ)) := by
    apply IsBigO.of_bound (2 * 3 ^ (2 / 9 : ℝ))
    filter_upwards [eventually_y_half_le_yNat,
        eventually_gt_atTop 0] with n hyFloor hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hthree :
        (3 * (n : ℝ)) ^ (2 / 9 : ℝ) =
          3 ^ (2 / 9 : ℝ) * y n := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hnR.le]
      rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ yNat n),
      hthree]
    have hyScaled : y n ≤ 2 * (yNat n : ℝ) := by linarith
    calc
      3 ^ (2 / 9 : ℝ) * y n ≤
          3 ^ (2 / 9 : ℝ) * (2 * (yNat n : ℝ)) :=
        mul_le_mul_of_nonneg_left hyScaled
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      _ = (2 * 3 ^ (2 / 9 : ℝ)) * (yNat n : ℝ) := by ring
  exact (hheadO.trans_isLittleO hmodel).trans_isBigO hscaledY

private theorem bankRoundingTailMajorant_isBigO_yNat :
    (fun n : ℕ ↦
      ((20 * bankRoundingDepth n * Nat.primeCounting (yNat n) : ℕ) : ℝ))
      =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ)) := by
  have hpnt0 :=
    SafePrimeCounting.primeCounting_nat_isEquivalent.comp_tendsto
      yNat_tendsto_atTop
  have hpnt :
      (fun n : ℕ ↦ (Nat.primeCounting (yNat n) : ℝ)) =O[atTop]
        (fun n : ℕ ↦
          (yNat n : ℝ) / Real.log (yNat n : ℝ)) := by
    simpa only [Function.comp_apply] using hpnt0.isBigO
  have hmul := bankRoundingDepth_isBigO_log_yNat.mul hpnt
  have hcore :
      (fun n : ℕ ↦
        (bankRoundingDepth n : ℝ) * Nat.primeCounting (yNat n)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ)) := by
    apply hmul.congr' (Eventually.of_forall fun _n ↦ rfl)
    filter_upwards [yNat_tendsto_atTop.eventually (eventually_gt_atTop 1)]
        with n hY
    have hlog : Real.log (yNat n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hY)).ne'
    field_simp
  have h20 := hcore.const_mul_left (20 : ℝ)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using h20

/-- The exact common request demand is `O(floor(n^(2/9)))`. -/
theorem bankBottomPaperDemand_isBigO_yNat :
    (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ)) := by
  have hmajorantPoint :
      (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (bankBottomPaperDemandMajorant n : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankBottomPaperDemand n),
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankBottomPaperDemandMajorant n), one_mul]
    exact_mod_cast bankBottomPaperDemand_le_majorant n
  have hmajorant :
      (fun n : ℕ ↦ (bankBottomPaperDemandMajorant n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ)) := by
    have hadd := (bankRoundingHeadMajorant_isLittleO_yNat.isBigO).add
      bankRoundingTailMajorant_isBigO_yNat
    apply hadd.congr'
    · exact Eventually.of_forall fun n ↦ by
        unfold bankBottomPaperDemandMajorant
        push_cast
        ring
    · exact Eventually.of_forall fun _n ↦ rfl
  exact hmajorantPoint.trans hmajorant











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

/-- Verifiable local geometry sufficient both for rough-signature equality and
large-prime marker recovery. -/
theorem eventually_bankBottom_three_mul_yNat_le_self :
    ∀ᶠ n : ℕ in atTop, 3 * yNat n ≤ n := by
  have hmodel : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (-(7 / 9 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 7 / 9)).comp
        tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun n : ℕ ↦ y n / (n : ℝ)) atTop (nhds 0) := by
    apply hmodel.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    symm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [y]
    calc
      (n : ℝ) ^ (2 / 9 : ℝ) / (n : ℝ) =
          (n : ℝ) ^ ((2 / 9 : ℝ) - 1) := by
        rw [Real.rpow_sub hnR, Real.rpow_one]
      _ = (n : ℝ) ^ (-(7 / 9 : ℝ)) := by norm_num
  have hsmall := hratio.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratioN hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hySmall : 3 * y n < (n : ℝ) := by
    have := (div_lt_iff₀ hnR).mp hratioN
    nlinarith
  have hcast : ((3 * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hcast



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryConcreteDemand -/
section


/-!
# Concrete ordinary-component requests and their demand

For every signed rounding slot, this file materializes one request for every
nonterminal source of its actual core path.  A request is routed by its exact
geometric-grid index and by the sign of the slot.  The request fibers are
finite sigma types, not cardinality placeholders.

The path congestion bounds give `17 * sum beta` at each small scale and the
sharp `2 * sum beta` at every large scale.  Finally the already audited
`O(yNat)` beta reserve is compared with the worst ordinary marker scale
`(n/log n)/yNat`; this is the uniform little-o estimate required by all moving
grid scales `Q <= yNat`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section





















/-! ## Exact request-fiber cardinality -/

















/-! ## The beta reserve against the worst moving ordinary scale -/



theorem yNat_div_bankOrdinaryWorstMarkerScale_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ (yNat n : ℝ) / bankOrdinaryWorstMarkerScale n)
      atTop (nhds 0) := by
  have hsqueeze : Tendsto
      (fun n : ℕ ↦ (yNat n : ℝ) /
        bankOrdinaryWorstMarkerScale n) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds Erdos390.Full.Scale.tendsto_endpointRatio_zero
    · filter_upwards [eventually_gt_atTop 2] with n hn
      have hscale : 0 < bankOrdinaryWorstMarkerScale n := by
        rw [bankOrdinaryWorstMarkerScale]
        exact div_pos (secondOrderScale_pos (by omega)) (by positivity)
      exact div_nonneg (Nat.cast_nonneg _) hscale.le
    · filter_upwards [eventually_ge_atTop 3,
          Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
          with n hn hlogY
      have hnPos : (0 : ℝ) < n := by positivity
      have hL : 1 ≤ L n := by
        rw [L]
        exact (show (1 : ℝ) ≤ Real.log (n : ℝ) by
          have hthree : (3 : ℝ) ≤ n := by exact_mod_cast hn
          have : Real.exp 1 ≤ (n : ℝ) :=
            Real.exp_one_lt_three.le.trans hthree
          exact (Real.le_log_iff_exp_le hnPos).2 this)
      have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
      have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
      have hyNatOne : (1 : ℝ) ≤ yNat n := by
        have hlogPos : 0 < Real.log (yNat n : ℝ) := by
          have hLPos : 0 < L n := lt_of_lt_of_le (by norm_num) hL
          nlinarith
        exact ((Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogPos).le
      have hmax : max 1 (yNat n : ℝ) = yNat n := max_eq_right hyNatOne
      rw [bankOrdinaryWorstMarkerScale, secondOrderScale, hmax]
      have hyNatPos : (0 : ℝ) < yNat n := lt_of_lt_of_le (by norm_num) hyNatOne
      have hLPos : 0 < L n := lt_of_lt_of_le (by norm_num) hL
      rw [show Real.log (n : ℝ) = L n by rfl]
      have hidentity :
          (yNat n : ℝ) / (((n : ℝ) / L n) / (yNat n : ℝ)) =
            (yNat n : ℝ) ^ 2 * L n / (n : ℝ) := by
        field_simp
      rw [hidentity, endpointRatio]
      apply div_le_div_of_nonneg_right _ hnPos.le
      calc
        (yNat n : ℝ) ^ 2 * L n ≤ y n ^ 2 * L n := by
          gcongr
        _ ≤ y n ^ 2 * L n ^ 2 := by
          have hySq : 0 ≤ y n ^ 2 := sq_nonneg _
          have hLsq : L n ≤ L n ^ 2 := by
            nlinarith [sq_nonneg (L n)]
          exact mul_le_mul_of_nonneg_left hLsq hySq
  exact hsqueeze















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









/-- The public reserve interface for guarding every ordinary marker at once:
an `O(yNat²)` family consumes `o(secondOrderScale)` positions. -/
theorem yNat_sq_div_secondOrderScale_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2 / secondOrderScale n)
      atTop (nhds 0) := by
  apply yNat_div_bankOrdinaryWorstMarkerScale_tendsto_zero.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hyNatOne : 1 ≤ yNat n := by
    rw [yNat]
    apply Nat.le_floor
    rw [y]
    have hnOneR : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 1 ≤ n by omega)
    simpa only [Nat.cast_one] using
      Real.one_le_rpow hnOneR
        (by norm_num : (0 : ℝ) ≤ 2 / 9)
  have hyNatPos : 0 < yNat n :=
    lt_of_lt_of_le Nat.zero_lt_one hyNatOne
  have hyPos : (0 : ℝ) < yNat n := by exact_mod_cast hyNatPos
  have hsecond : 0 < secondOrderScale n := secondOrderScale_pos hn
  rw [bankOrdinaryWorstMarkerScale,
    max_eq_right (by exact_mod_cast hyNatOne : (1 : ℝ) ≤ yNat n)]
  field_simp [hyPos.ne', hsecond.ne']



/-! ## Arithmetic helpers for rough signatures -/









/-! ## Marker injectivity inherited from the orientation pools -/









/-! ## The public realization object and its actual factors -/



namespace BankOrdinaryPaperRealization











































































/-! ## The three actual occurrences and global collision-freedom -/







































/-! ## Realized component and signed-slot changes -/























end BankOrdinaryPaperRealization

/-! ## Eventual realized allocation -/



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





/-! ## A literal logarithmic path budget -/

















/-! ## The full actual marker/component census -/







namespace BankPaperRealization





end BankPaperRealization

/-! ## The paper-sized `O(yL)` asymptotic -/

/-- The moving geometric-grid index below `yNat` is logarithmic. -/
theorem bankOrdinaryScaleIndex_yNat_le_log
    {n : ℕ} (hy : 6 ≤ yNat n) (hgeometry : 3 * yNat n ≤ n) :
    (bankOrdinaryScaleIndex (yNat n) : ℝ) ≤
      L n / Real.log (4 / 3 : ℝ) := by
  let j := bankOrdinaryScaleIndex (yNat n)
  have hcell := bankOrdinaryScaleIndex_cell
    (show 5 ≤ yNat n by omega)
  have hscaleQ : bankOrdinaryScale j < (yNat n : ℚ) := by
    simpa only [j] using hcell.1
  have hscaleR : (bankOrdinaryScale j : ℝ) < (yNat n : ℝ) := by
    exact_mod_cast hscaleQ
  have hscaleExpanded :
      (4 : ℝ) * (4 / 3 : ℝ) ^ j < (yNat n : ℝ) := by
    simpa only [bankOrdinaryScale, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_div] using hscaleR
  have hpowPos : 0 < (4 / 3 : ℝ) ^ j := by positivity
  have hpowLt : (4 / 3 : ℝ) ^ j < (yNat n : ℝ) := by
    have hpowLe : (4 / 3 : ℝ) ^ j ≤
        4 * (4 / 3 : ℝ) ^ j := by nlinarith
    exact hpowLe.trans_lt hscaleExpanded
  have hlogPow := Real.log_lt_log hpowPos hpowLt
  rw [Real.log_pow] at hlogPow
  have hbaseLog : 0 < Real.log (4 / 3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hyLe : yNat n ≤ n := by omega
  have hyPos : (0 : ℝ) < yNat n := by positivity
  have hlogY : Real.log (yNat n : ℝ) ≤ L n := by
    rw [L]
    exact Real.log_le_log hyPos (by exact_mod_cast hyLe)
  apply (le_div_iff₀ hbaseLog).2
  have hcast : (j : ℝ) =
      (bankOrdinaryScaleIndex (yNat n) : ℝ) := rfl
  rw [← hcast]
  exact hlogPow.le.trans hlogY

theorem bankOrdinaryPathComponentBudget_isBigO_L :
    (fun n : ℕ ↦ (bankOrdinaryPathComponentBudget n : ℝ))
      =O[atTop] L := by
  let C : ℝ := 2 * (1 / Real.log (4 / 3 : ℝ)) + 17
  apply IsBigO.of_bound C
  filter_upwards [eventually_bankBottom_six_le_yNat,
      eventually_bankBottom_three_mul_yNat_le_self,
      eventually_ge_atTop 3] with n hy hgeometry hn
  have hindex := bankOrdinaryScaleIndex_yNat_le_log hy hgeometry
  have hL : 1 ≤ L n := by
    rw [L]
    have hnR : (Real.exp 1 : ℝ) ≤ n :=
      Real.exp_one_lt_three.le.trans (by exact_mod_cast hn)
    exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < n)).2 hnR
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ bankOrdinaryPathComponentBudget n),
    Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hL)]
  have hindex' : (bankOrdinaryScaleIndex (yNat n) : ℝ) ≤
      (1 / Real.log (4 / 3 : ℝ)) * L n := by
    simpa only [one_div, inv_mul_eq_div] using hindex
  dsimp only [C]
  calc
    (bankOrdinaryPathComponentBudget n : ℝ) =
        17 + 2 *
          ((bankOrdinaryScaleIndex (yNat n) - 5 : ℕ) : ℝ) := by
      simp only [bankOrdinaryPathComponentBudget, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ 17 + 2 *
        (bankOrdinaryScaleIndex (yNat n) : ℝ) := by
      gcongr
      exact_mod_cast
        (Nat.sub_le (bankOrdinaryScaleIndex (yNat n)) 5)
    _ ≤ 17 + 2 *
        ((1 / Real.log (4 / 3 : ℝ)) * L n) := by
      gcongr
    _ ≤ 17 * L n + 2 *
        ((1 / Real.log (4 / 3 : ℝ)) * L n) := by
      nlinarith
    _ = (2 * (1 / Real.log (4 / 3 : ℝ)) + 17) * L n := by
      ring

/-- The sharp actual marker budget has size `O(yNat * L)` as soon as the
one-sided beta demand is `O(yNat)`.  All finite path and component counting
has already been discharged before this analytic input is introduced. -/
theorem bankPaperSharpMarkerBudget_isBigO_yNat_mul_L_of_demand
    (hDemand :
      (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ))) :
    (fun n : ℕ ↦ (bankPaperSharpMarkerBudget n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ) * L n) := by
  have htwoPath :=
    bankOrdinaryPathComponentBudget_isBigO_L.const_mul_left (2 : ℝ)
  have height : (fun _n : ℕ ↦ (8 : ℝ)) =O[atTop] L := by
    apply IsBigO.of_bound 8
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hL : 1 ≤ L n := by
      rw [L]
      have hnR : (Real.exp 1 : ℝ) ≤ n :=
        Real.exp_one_lt_three.le.trans (by exact_mod_cast hn)
      exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < n)).2 hnR
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8),
      Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hL)]
    nlinarith
  have hfactorModel := htwoPath.add height
  have hfactor :
      (fun n : ℕ ↦
        ((2 * bankOrdinaryPathComponentBudget n + 8 : ℕ) : ℝ))
          =O[atTop] L := by
    apply hfactorModel.congr'
    · exact Eventually.of_forall fun n ↦ by
        push_cast
        rfl
    · exact Eventually.of_forall fun _n ↦ rfl
  have hproduct := hDemand.mul hfactor
  apply hproduct.congr'
  · exact Eventually.of_forall fun n ↦ by
      simp only [bankPaperSharpMarkerBudget, Nat.cast_mul,
        Nat.cast_add, Nat.cast_ofNat]
  · exact Eventually.of_forall fun _n ↦ rfl

/-- The unconditional paper-sized census.  Its sole prime-counting input is
the existing safe-PNT consequence `bankBottomPaperDemand_isBigO_yNat`. -/
theorem bankPaperSharpMarkerBudget_isBigO_yNat_mul_L :
    (fun n : ℕ ↦ (bankPaperSharpMarkerBudget n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ) * L n) :=
  bankPaperSharpMarkerBudget_isBigO_yNat_mul_L_of_demand
    bankBottomPaperDemand_isBigO_yNat

/-! ## Sharp numerical-guard corollaries -/

namespace BankPaperRealization









end BankPaperRealization

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

































/-! ## Full density and logarithmic first moment -/









/-! A powerset moment inequality.  It is the finite probabilistic estimate
behind the truncation: the first moment of independent nonnegative local
weights is at most their partition function times `sum b_p a_p`. -/





/-! ## Prime sums at the rough-head modulus -/











/-! ## Mertens lower bound for the full Euler product -/



















/-! ## Retaining a fixed fraction below level `y^2` -/





/-! ## A universal `exp 4` coefficient-mean bound -/















/-! ## The canonical Lambda norm -/







/-! ## Fixed eventual constants and the closed interval theorem -/





theorem tangentSelbergCanonicalMainConstant_pos :
    0 < tangentSelbergCanonicalMainConstant := by
  unfold tangentSelbergCanonicalMainConstant
  positivity













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













/-! ## The harmonic main term -/





/-! ## Moving-scale negligibility -/

/-- The paper smoothness cutoff `yNat` is `o(n)`.  We derive this from the already
audited stronger estimate `yNat^2 = o(n/log n)`. -/
theorem tangentPaper_yNat_div_self_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (yNat n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  apply squeeze_zero'
    (g := fun n : ℕ ↦ (yNat n : ℝ) ^ 2 / secondOrderScale n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    positivity
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hnR : (0 : ℝ) < n := by positivity
    have hL : 1 ≤ L n := by
      rw [L]
      have hnCast : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hexp : Real.exp 1 ≤ (n : ℝ) :=
        Real.exp_one_lt_three.le.trans hnCast
      exact (Real.le_log_iff_exp_le hnR).2 hexp
    have hyOneNat : 1 ≤ yNat n := by
      rw [yNat]
      apply Nat.le_floor
      rw [y]
      have hnOneR : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show 1 ≤ n by omega)
      simpa only [Nat.cast_one] using
        Real.one_le_rpow hnOneR
          (by norm_num : (0 : ℝ) ≤ 2 / 9)
    have hyOne : (1 : ℝ) ≤ yNat n := by exact_mod_cast hyOneNat
    have hySq : (yNat n : ℝ) ≤ (yNat n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((yNat n : ℝ) - 1)]
    have hySqL : (yNat n : ℝ) ^ 2 ≤
        (yNat n : ℝ) ^ 2 * L n := by
      exact le_mul_of_one_le_right (sq_nonneg _) hL
    have hidentity :
        (yNat n : ℝ) ^ 2 / secondOrderScale n =
          (yNat n : ℝ) ^ 2 * L n / (n : ℝ) := by
      unfold secondOrderScale
      change (yNat n : ℝ) ^ 2 / ((n : ℝ) / L n) = _
      have hLPos : 0 < L n :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL
      field_simp [hnR.ne', hLPos.ne']
    rw [hidentity]
    exact div_le_div_of_nonneg_right (hySq.trans hySqL) hnR.le
  · exact yNat_sq_div_secondOrderScale_tendsto_zero

/-- The sharp paper guard deletion, even after multiplication by the largest
permitted label, is `o(n)`. -/
theorem tangentPaperSharpDeletion_mul_yNat_div_self_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) *
          (yNat n : ℝ)) / (n : ℝ))
      atTop (nhds 0) := by
  have hmodelLittle :
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2 * L n) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ)) := by
    apply (isLittleO_iff_tendsto' ?_).mpr
    · apply yNat_sq_div_secondOrderScale_tendsto_zero.congr'
      filter_upwards [eventually_gt_atTop 1] with n hn
      have hnR : (0 : ℝ) < n := by positivity
      have hL : 0 < L n := L_pos hn
      unfold secondOrderScale
      rw [show Real.log (n : ℝ) = L n by rfl]
      field_simp [hnR.ne', hL.ne']
    · filter_upwards [eventually_gt_atTop 0] with n hn hzero
      have hnNe : (n : ℝ) ≠ 0 := by positivity
      exact (hnNe hzero).elim
  have hproductRaw :=
    bankPaperSharpMarkerBudget_isBigO_yNat_mul_L.mul
      (isBigO_refl (fun n : ℕ ↦ (yNat n : ℝ)) atTop)
  have hproduct :
      (fun n : ℕ ↦
        (bankPaperSharpMarkerBudget n : ℝ) * (yNat n : ℝ))
        =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ) ^ 2 * L n) := by
    apply hproductRaw.congr'
    · exact Eventually.of_forall fun _n ↦ rfl
    · exact Eventually.of_forall fun _n ↦ by ring
  have hbudget : Tendsto
      (fun n : ℕ ↦
        ((bankPaperSharpMarkerBudget n : ℝ) * (yNat n : ℝ)) /
          (n : ℝ)) atTop (nhds 0) :=
    (hproduct.trans_isLittleO hmodelLittle).tendsto_div_nhds_zero
  have hone := tangentPaper_yNat_div_self_tendsto_zero.const_mul (4 : ℝ)
  have hbudgetFour := hbudget.const_mul (4 : ℝ)
  have hsum : Tendsto
      (fun n : ℕ ↦
        4 * ((yNat n : ℝ) / (n : ℝ)) +
          4 * (((bankPaperSharpMarkerBudget n : ℝ) * (yNat n : ℝ)) /
            (n : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hone.add hbudgetFour
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  push_cast
  ring

/-! ## Eventual exceptional-loss absorption -/





/-! ## The fixed-head candidate at the paper endpoints -/



/-- With `h=ceil(c n/log n)`, the candidate main term retains three quarters
of the fixed head gap, uniformly over every permitted endpoint pair. -/
theorem eventually_tangentRoughHeadCandidateMain_normalized_ge_three_quarters
    (W K : ℕ) {c r0 : ℝ}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ u v : ℕ,
      0 < u → 0 < v → u ≤ yNat n →
      (u : ℝ) / (v : ℝ) ≤ r0 →
      n / v ≤ tangentBroadUpper n K (upperTailLength c n) / u ∧
        3 * tangentPaperHeadGap W r0 / 4 ≤
          (u : ℝ) / (n : ℝ) *
            tangentRoughHeadCandidateMain
              W n K (upperTailLength c n) u v := by
  let d : ℝ := roughHeadDensity W
  let P : ℝ := roughHeadModulus W
  let gap : ℝ := tangentPaperHeadGap W r0
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact tangentPaperHeadGap_pos W (hr0three.trans (by norm_num))
  have htailT : Tendsto
      (fun n : ℕ ↦ d *
        (((K * upperTailLength c n : ℕ) : ℝ) / (n : ℝ)))
      atTop (nhds 0) := by
    have h := (upperTailLength_ratio_tendsto_zero hc).const_mul
      (d * (K : ℝ))
    simpa only [mul_zero] using h.congr' (Eventually.of_forall fun n ↦ by
      push_cast
      ring)
  have hheadT : Tendsto
      (fun n : ℕ ↦
        ((yNat n : ℝ) / (n : ℝ)) * (d + P))
      atTop (nhds 0) := by
    have h := tangentPaper_yNat_div_self_tendsto_zero.const_mul (d + P)
    simpa only [mul_zero, zero_mul, mul_comm] using h
  have htailSmall := htailT.eventually
    (eventually_lt_nhds (div_pos hgap (by norm_num : (0 : ℝ) < 16)))
  have hheadSmall := hheadT.eventually
    (eventually_lt_nhds (div_pos hgap (by norm_num : (0 : ℝ) < 16)))
  filter_upwards [eventually_gt_atTop 0, htailSmall, hheadSmall]
    with n hn htail hhead
  intro u v hu hv huy hratio
  have hd : 0 < d := by
    dsimp only [d]
    exact roughHeadDensity_pos W
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast roughHeadModulus_pos W
  have huBound :
      (u : ℝ) / (n : ℝ) * (d + P) ≤
        (yNat n : ℝ) / (n : ℝ) * (d + P) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hdiv : (u : ℝ) / (n : ℝ) ≤
        (yNat n : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast huy) hnR.le
    exact mul_le_mul_of_nonneg_right hdiv (add_nonneg hd.le hP.le)
  apply tangentRoughHeadCandidateMain_normalized_ge_three_quarters
    (W := W) hn hu hv hr0one (hr0three.trans (by norm_num)) hratio
  · simpa only [d, gap] using htail.le
  · simpa only [d, P, gap] using huBound.trans hhead.le

/-! ## The literal candidate floor absorbs every canonical loss -/

/-- Section 9's literal parameter choices discharge the last arithmetic
comparison left open by `TangentCanonicalCleanListLower`.  The conclusion is
the exact natural-number inequality consumed by the canonical clean-list
bridge; neither it nor a disguised copy is assumed.

The bookkeeping reserves `1/8` of the head gap for the effective-card
ceiling, `3/8` for the canonical exceptional ceiling, and `1/16` for the
sharp deterministic deletion.  Their total `9/16` is strictly below the
`3/4` retained by the fixed-head candidate. -/
theorem eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses
    (W K : ℕ) {c r0 deltaStar : ℝ}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop, ∀ u v : ℕ,
      0 < u → 0 < v → v ≤ u → u ≤ yNat n →
      (u : ℝ) / (v : ℝ) ≤ r0 →
      n / v ≤ tangentBroadUpper n K (upperTailLength c n) / u ∧
        tangentEffectiveLowerCard
              (tangentPaperCleanListDensity W r0) n v +
            tangentCanonicalExceptionalNatUpper n K
              (upperTailLength c n)
              (tangentPaperExceptionalCutoff deltaStar n)
              (yNat n) u v +
            4 + 4 * bankPaperSharpMarkerBudget n ≤
          tangentRoughHeadCandidateLower W n K
            (upperTailLength c n) u v := by
  let gap : ℝ := tangentPaperHeadGap W r0
  let density : ℝ := tangentPaperCleanListDensity W r0
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact tangentPaperHeadGap_pos W (hr0three.trans (by norm_num))
  have hdensity : density = gap / 16 := by
    simp only [density, gap, tangentPaperCleanListDensity]
  have hdensityPos : 0 < density := by
    rw [hdensity]
    positivity
  have hcandidate :=
    eventually_tangentRoughHeadCandidateMain_normalized_ge_three_quarters
      W K hc hr0one hr0three
  have hexceptionalMain :=
    eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap
      hdelta hmainSmall
  have hexceptionalRemainder :=
    eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap
      hdelta.le hdeltaUpper (by simpa only [gap] using hgap)
  have hySmall := tangentPaper_yNat_div_self_tendsto_zero.eventually
    (eventually_lt_nhds (div_pos hgap (by norm_num : (0 : ℝ) < 64)))
  have hsharpSmall :=
    tangentPaperSharpDeletion_mul_yNat_div_self_tendsto_zero.eventually
      (eventually_lt_nhds
        (div_pos hgap (by norm_num : (0 : ℝ) < 16)))
  filter_upwards
    [hcandidate, hexceptionalMain, hexceptionalRemainder,
      hySmall, hsharpSmall, eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
      with n hcandidateN hexceptionalMainN hexceptionalRemainderN
        hySmallN hsharpSmallN hn hlogY
  intro u v hu hv hvu huy hratio
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hfactorPos : 0 < (u : ℝ) / (n : ℝ) := div_pos huR hnR
  have hfactorY :
      (u : ℝ) / (n : ℝ) ≤ (yNat n : ℝ) / (n : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast huy) hnR.le
  have hfactorSmall :
      (u : ℝ) / (n : ℝ) ≤ gap / 64 := by
    exact hfactorY.trans (by simpa only [gap] using hySmallN.le)
  have hcandidateUV := hcandidateN u v hu hv huy hratio
  refine ⟨hcandidateUV.1, ?_⟩

  have heffectiveArg :
      0 ≤ density * (n : ℝ) / (v : ℝ) := by positivity
  have heffectiveCeil :
      (tangentEffectiveLowerCard density n v : ℝ) ≤
        density * (n : ℝ) / (v : ℝ) + 1 := by
    unfold tangentEffectiveLowerCard
    exact (Nat.ceil_lt_add_one heffectiveArg).le
  have heffectiveNormalized :
      (u : ℝ) / (n : ℝ) *
          (tangentEffectiveLowerCard density n v : ℝ) ≤
        gap / 8 := by
    calc
      (u : ℝ) / (n : ℝ) *
          (tangentEffectiveLowerCard density n v : ℝ) ≤
          (u : ℝ) / (n : ℝ) *
            (density * (n : ℝ) / (v : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left heffectiveCeil hfactorPos.le
      _ = density * ((u : ℝ) / (v : ℝ)) +
          (u : ℝ) / (n : ℝ) := by
        field_simp [hnR.ne', hvR.ne']
      _ ≤ density * r0 + gap / 64 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hratio hdensityPos.le)
          hfactorSmall
      _ ≤ gap / 8 := by
        rw [hdensity]
        calc
          gap / 16 * r0 + gap / 64 ≤
              gap / 16 * (3 / 2 : ℝ) + gap / 64 :=
            add_le_add_left
              (mul_le_mul_of_nonneg_left hr0three.le
                (div_nonneg hgap.le (by norm_num : (0 : ℝ) ≤ 16))) _
          _ ≤ gap / 8 := by linarith

  have hLPos : 0 < L n := L_pos (by omega)
  have hlogYPos : 0 < Real.log (yNat n : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hLPos).trans_le hlogY
  have hlengthNonneg : 0 ≤
      tangentCanonicalExceptionalLengthSum n K (upperTailLength c n)
        (tangentPaperExceptionalCutoff deltaStar n) u v := by
    unfold tangentCanonicalExceptionalLengthSum
    positivity
  have hremainderNonneg : 0 ≤
      tangentCanonicalExceptionalRemainder
        (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u := by
    unfold tangentCanonicalExceptionalRemainder
    positivity
  have hexceptionalUpperNonneg : 0 ≤
      tangentCanonicalExceptionalUpper n K (upperTailLength c n)
        (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v := by
    unfold tangentCanonicalExceptionalUpper
    exact add_nonneg
      (mul_nonneg hlengthNonneg
        (div_nonneg tangentSelbergCanonicalMainConstant_pos.le
          hlogYPos.le))
      hremainderNonneg
  have hexceptionalReal :
      (u : ℝ) / (n : ℝ) *
          tangentCanonicalExceptionalUpper n K (upperTailLength c n)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v ≤
        5 * gap / 16 := by
    have hmain := hexceptionalMainN K (upperTailLength c n) u v hu
    have hremainder := hexceptionalRemainderN u hu
    unfold tangentCanonicalExceptionalUpper
    calc
      (u : ℝ) / (n : ℝ) *
          (tangentCanonicalExceptionalLengthSum n K (upperTailLength c n)
              (tangentPaperExceptionalCutoff deltaStar n) u v *
                (tangentSelbergCanonicalMainConstant /
                  Real.log (yNat n : ℝ)) +
            tangentCanonicalExceptionalRemainder
              (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u) =
          (u : ℝ) / (n : ℝ) *
              (tangentCanonicalExceptionalLengthSum n K
                (upperTailLength c n)
                (tangentPaperExceptionalCutoff deltaStar n) u v *
                  (tangentSelbergCanonicalMainConstant /
                    Real.log (yNat n : ℝ))) +
            (u : ℝ) / (n : ℝ) *
              tangentCanonicalExceptionalRemainder
                (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u := by
        ring
      _ ≤ gap / 4 + gap / 16 := by
        exact add_le_add
          (by simpa only [gap] using hmain)
          (by simpa only [gap] using hremainder)
      _ = 5 * gap / 16 := by ring
  have hexceptionalCeil :
      (tangentCanonicalExceptionalNatUpper n K (upperTailLength c n)
          (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v : ℝ) ≤
        tangentCanonicalExceptionalUpper n K (upperTailLength c n)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v + 1 := by
    unfold tangentCanonicalExceptionalNatUpper
    exact (Nat.ceil_lt_add_one hexceptionalUpperNonneg).le
  have hexceptionalNormalized :
      (u : ℝ) / (n : ℝ) *
          (tangentCanonicalExceptionalNatUpper n K (upperTailLength c n)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v : ℝ) ≤
        3 * gap / 8 := by
    calc
      (u : ℝ) / (n : ℝ) *
          (tangentCanonicalExceptionalNatUpper n K (upperTailLength c n)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v : ℝ) ≤
          (u : ℝ) / (n : ℝ) *
            (tangentCanonicalExceptionalUpper n K (upperTailLength c n)
              (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v + 1) :=
        mul_le_mul_of_nonneg_left hexceptionalCeil hfactorPos.le
      _ = (u : ℝ) / (n : ℝ) *
            tangentCanonicalExceptionalUpper n K (upperTailLength c n)
              (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v +
          (u : ℝ) / (n : ℝ) := by ring
      _ ≤ 5 * gap / 16 + gap / 64 :=
        add_le_add hexceptionalReal hfactorSmall
      _ ≤ 3 * gap / 8 := by linarith

  have hsharpNormalized :
      (u : ℝ) / (n : ℝ) *
          ((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) ≤
        gap / 16 := by
    calc
      (u : ℝ) / (n : ℝ) *
          ((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) =
        ((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) *
            (u : ℝ) / (n : ℝ) := by ring
      _ ≤ ((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) *
            (yNat n : ℝ) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast huy)
            (Nat.cast_nonneg _)) hnR.le
      _ ≤ gap / 16 := by
        exact (by simpa only [gap] using hsharpSmallN.le)

  let effective : ℕ := tangentEffectiveLowerCard density n v
  let exceptional : ℕ :=
    tangentCanonicalExceptionalNatUpper n K (upperTailLength c n)
      (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v
  let deletion : ℕ := 4 + 4 * bankPaperSharpMarkerBudget n
  have hlossCast :
      (((effective + exceptional + 4 +
          4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ)) =
        (effective : ℝ) + (exceptional : ℝ) + (deletion : ℝ) := by
    dsimp only [deletion]
    push_cast
    ring
  have hlossNormalized :
      (u : ℝ) / (n : ℝ) *
          ((effective + exceptional + 4 +
            4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) ≤
        9 * gap / 16 := by
    rw [hlossCast]
    calc
      (u : ℝ) / (n : ℝ) *
          ((effective : ℝ) + (exceptional : ℝ) + (deletion : ℝ)) =
        (u : ℝ) / (n : ℝ) * (effective : ℝ) +
          (u : ℝ) / (n : ℝ) * (exceptional : ℝ) +
          (u : ℝ) / (n : ℝ) * (deletion : ℝ) := by ring
      _ ≤ gap / 8 + 3 * gap / 8 + gap / 16 := by
        exact add_le_add
          (add_le_add
            (by simpa only [effective] using heffectiveNormalized)
            (by simpa only [exceptional] using hexceptionalNormalized))
          (by simpa only [deletion] using hsharpNormalized)
      _ = 9 * gap / 16 := by ring
  have hlossBelowCandidateNormalized :
      (u : ℝ) / (n : ℝ) *
          ((effective + exceptional + 4 +
            4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) ≤
        (u : ℝ) / (n : ℝ) *
          tangentRoughHeadCandidateMain W n K (upperTailLength c n) u v := by
    exact hlossNormalized.trans
      ((by nlinarith : 9 * gap / 16 ≤ 3 * gap / 4).trans
        (by simpa only [gap] using hcandidateUV.2))
  have hlossBelowCandidate :
      ((effective + exceptional + 4 +
        4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) ≤
          tangentRoughHeadCandidateMain W n K (upperTailLength c n) u v :=
    le_of_mul_le_mul_left hlossBelowCandidateNormalized hfactorPos
  change effective + exceptional + 4 + 4 * bankPaperSharpMarkerBudget n ≤
    tangentRoughHeadCandidateLower W n K (upperTailLength c n) u v
  unfold tangentRoughHeadCandidateLower
  apply Nat.le_floor
  exact hlossBelowCandidate.trans (le_max_right 0 _)

/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_009 := by
  exact @Erdos390.WholePaper.eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses
