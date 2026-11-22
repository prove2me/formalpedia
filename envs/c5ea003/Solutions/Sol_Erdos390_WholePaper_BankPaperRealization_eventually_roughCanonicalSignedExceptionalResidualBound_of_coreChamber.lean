-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalSignedExceptionalResidualBound_of_coreChamber
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:21:39.738421+00:00
-- url     : https://prove2.me/submissions/957961f6-be44-4eb0-a39f-83e00b9661c4

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_abs_roughCanonicalSignedExceptionalResidual_le_coreFirstFinite

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

















/-! ## The finite Selberg output and its normalized remainder -/











/-! ## The endpoint remainder tends to zero -/





/-! ## Uniform packaging of the finite majorant -/

/-- Eventually the literal tail ceiling is at most `2cN`. -/
theorem eventually_upperTailLength_cast_le_two_mul_secondOrderScale
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) ≤
        2 * c * secondOrderScale n := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) / secondOrderScale n ≤
        2 * c :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_le_nhds (by linarith : c < 2 * c))
  filter_upwards [hratio, eventually_secondOrderScale_pos] with n hn hscale
  exact (div_le_iff₀ hscale).mp hn

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







/-! ## Closing the finite weighted Selberg estimate -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalCoreFirst -/
section


/-!
# Core-first cancellation for the signed exceptional residual

The exceptional term in Section 9 cannot be estimated by separating its
positive and negative halves.  The paper first fixes the complete smooth
core `b`, sums all physical rough pieces with that core, and only then takes
absolute values.  This file makes that order of summation literal.

The first part is completely finite.  It partitions both halves of
`roughCanonicalSignedExceptionalResidual` by `completeSmoothPart (yNat n)`,
transfers every low-prime valuation to that smooth part, and reindexes both
halves over one common positive prefix.  Thus the sign in each core is the
actual upper cardinality minus the actual weighted lower mass.

The second part records the elementary fixed-head cancellation used on the
leading term.  Its periodic coefficient has uniformly bounded partial sums;
finite Abel summation therefore bounds it against every sequence with the
paper's prime-power-by-prime-power variation estimate.  No rough-counting
asymptotic is used in these arguments.

The last part isolates the one genuinely new analytic input: the signed
four-to-five-prime chamber expansion for a fixed smooth core, before any
valuation sum or triangle inequality.  All subsequent core, valuation, and
endpoint ledgers are finite consequences of that expansion.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.LocalFugacityBounds

noncomputable section

namespace BankPaperRealization

/-! ## The literal common smooth-core partition -/































/-! ## The fixed-head periodic coefficient -/

















/-! ## Finite Abel cancellation -/











/-! ## Prime-power expansion of the periodic leading ledger -/









/-! ## Elementary valuation ledgers for the analytic remainders -/









/-! ## The isolated four-to-five chamber input -/















/-! ## Endpoint absorption at the strict paper scale -/



/-- A positive exceptional exponent makes the natural cutoff tend to
infinity. -/
theorem tangentPaperExceptionalCutoff_tendsto_atTop
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (tangentPaperExceptionalCutoff deltaStar) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro A
  have hpower : Tendsto (fun n : Nat => (n : Real) ^ deltaStar)
      atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  have hpowerGe : ∀ᶠ n : Nat in atTop,
      (A : Real) ≤ (n : Real) ^ deltaStar :=
    hpower.eventually (eventually_ge_atTop (A : Real))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hpowerGe
  refine ⟨N, fun n hn => ?_⟩
  have hcut := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  exact_mod_cast (hN n hn).trans hcut

/-- The cutoff endpoint allowance `X0*L^2/n` tends to zero for every fixed
`deltaStar<1`. -/
theorem roughCanonicalExceptionalEndpointRatio_tendsto_zero
    {deltaStar : Real} (hdeltaUpper : deltaStar < 1) :
    Tendsto (roughCanonicalExceptionalEndpointRatio deltaStar)
      atTop (nhds 0) := by
  have hexponent : 0 < 1 - deltaStar := sub_pos.mpr hdeltaUpper
  have hrealMain : Tendsto
      (fun x : Real => Real.log x ^ (2 : Real) /
        x ^ (1 - deltaStar)) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : Real) hexponent).tendsto_div_nhds_zero
  have hmain : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real) ^ (1 - deltaStar))
      atTop (nhds 0) := by
    simpa [Function.comp_def, L, Real.rpow_natCast] using
      hrealMain.comp tendsto_natCast_atTop_atTop
  have hrealEndpoint : Tendsto
      (fun x : Real => Real.log x ^ (2 : Real) / x ^ (1 : Real))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : Real)
      (by norm_num : (0 : Real) < 1)).tendsto_div_nhds_zero
  have hendpoint : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (nhds 0) := by
    simpa [Function.comp_def, L, Real.rpow_natCast, Real.rpow_one] using
      hrealEndpoint.comp tendsto_natCast_atTop_atTop
  have hmodel : Tendsto
      (fun n : Nat => ((n : Real) ^ deltaStar + 1) * L n ^ 2 /
        (n : Real)) atTop (nhds 0) := by
    have hadd := hmain.add hendpoint
    have heq :
        (fun n : Nat =>
            L n ^ 2 / (n : Real) ^ (1 - deltaStar) +
              L n ^ 2 / (n : Real)) =ᶠ[atTop]
          (fun n : Nat =>
            ((n : Real) ^ deltaStar + 1) * L n ^ 2 / (n : Real)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
      have hpowPos : (0 : Real) < (n : Real) ^ (1 - deltaStar) :=
        Real.rpow_pos_of_pos hnReal _
      have hpow :
          (n : Real) ^ deltaStar * (n : Real) ^ (1 - deltaStar) =
            (n : Real) := by
        rw [← Real.rpow_add hnReal]
        ring_nf
        exact Real.rpow_one _
      have hquot :
          (n : Real) ^ deltaStar / (n : Real) =
            1 / (n : Real) ^ (1 - deltaStar) := by
        calc
          (n : Real) ^ deltaStar / (n : Real) =
              ((n : Real) ^ deltaStar * (n : Real) ^ (1 - deltaStar)) /
                ((n : Real) * (n : Real) ^ (1 - deltaStar)) := by
            field_simp [hnReal.ne', hpowPos.ne']
          _ = (n : Real) /
                ((n : Real) * (n : Real) ^ (1 - deltaStar)) := by rw [hpow]
          _ = 1 / (n : Real) ^ (1 - deltaStar) := by
            field_simp [hnReal.ne', hpowPos.ne']
      calc
        L n ^ 2 / (n : Real) ^ (1 - deltaStar) +
            L n ^ 2 / (n : Real) =
          ((n : Real) ^ deltaStar / (n : Real)) * L n ^ 2 +
            L n ^ 2 / (n : Real) := by rw [hquot]; ring
        _ = ((n : Real) ^ deltaStar + 1) * L n ^ 2 /
            (n : Real) := by ring
    simpa using hadd.congr' heq
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop 0] with n hn
    unfold roughCanonicalExceptionalEndpointRatio
    positivity
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hnReal : (0 : Real) < (n : Real) := by positivity
    have hcut := tangentPaperExceptionalCutoff_cast_lt_add_one
      deltaStar n
    unfold roughCanonicalExceptionalEndpointRatio
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcut.le (sq_nonneg (L n))) hnReal.le
  · exact hmodel

/-- Eventually every exceptional endpoint `+1` is absorbed by
`n/L^2`. -/
theorem eventually_tangentPaperExceptionalCutoff_le_self_div_L_sq
    {deltaStar : Real} (hdeltaUpper : deltaStar < 1) :
    ∀ᶠ n : Nat in atTop,
      (tangentPaperExceptionalCutoff deltaStar n : Real) ≤
        (n : Real) / L n ^ 2 := by
  have hratio : ∀ᶠ n : Nat in atTop,
      roughCanonicalExceptionalEndpointRatio deltaStar n ≤ 1 :=
    (roughCanonicalExceptionalEndpointRatio_tendsto_zero hdeltaUpper).eventually
      (eventually_le_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hratio, eventually_gt_atTop 1] with n hnRatio hn
  have hnReal : (0 : Real) < (n : Real) := by positivity
  have hL : 0 < L n := L_pos hn
  unfold roughCanonicalExceptionalEndpointRatio at hnRatio
  have hproduct :
      (tangentPaperExceptionalCutoff deltaStar n : Real) * L n ^ 2 ≤
        (n : Real) := by
    have hratioProduct := (div_le_iff₀ hnReal).mp hnRatio
    simpa only [one_mul] using hratioProduct
  exact (le_div_iff₀ (sq_pos_of_pos hL)).2 hproduct

/-! ## Uniform paper-scale packaging -/







/-- Once the isolated four-to-five chamber estimate is supplied, all
remaining finite and asymptotic ledgers give the paper's strict
`N/(pL)` bound, uniformly for `W<p≤y`. -/
theorem eventually_roughCanonicalSignedExceptionalResidualBound_of_coreChamber
    {W K : Nat} {c deltaStar beta : Real}
    {deepConstant cutoffConstant variationConstant : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hdeep : 0 ≤ deepConstant) (hcutoff : 0 ≤ cutoffConstant)
    (hvariation : 0 ≤ variationConstant)
    (hchamber : RoughCanonicalSignedExceptionalCoreChamberEventually
      W K c deltaStar beta deepConstant cutoffConstant variationConstant) :
    ∀ᶠ n : Nat in atTop, ∀ p : Nat,
      p.Prime → W < p → p ≤ yNat n →
      RoughCanonicalSignedExceptionalResidualBound
        n (upperTailLength c n) K deltaStar
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          (roughHeadBalancedAlpha W n (upperTailLength c n) K beta (L n))
          beta (L n))
        p
        (roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
          deepConstant cutoffConstant variationConstant *
            secondOrderScale n / ((p : Real) * L n)) := by
  unfold RoughCanonicalSignedExceptionalCoreChamberEventually at hchamber
  have hcutTop := tangentPaperExceptionalCutoff_tendsto_atTop hdelta
  have hcutTwo : ∀ᶠ n : Nat in atTop,
      2 ≤ tangentPaperExceptionalCutoff deltaStar n :=
    hcutTop.eventually (eventually_ge_atTop 2)
  have hdeltaOne : deltaStar < 1 := hdeltaUpper.trans (by norm_num)
  filter_upwards [hchamber, eventually_ge_atTop 3,
      eventually_upperTailLength_le hc,
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      eventually_one_add_log_two_mul_exceptionalCutoff_le hdelta,
      eventually_tangentPaperExceptionalCutoff_le_self_div_L_sq hdeltaOne,
      hcutTwo]
      with n hnChamber hn htail htailScale hlogY hlogCut hendpoint hcut
  obtain ⟨kernelWeight, coreError, hcore⟩ := hnChamber
  intro p hp hWp hpY
  let rawWeight :=
    roughHeadCompatibleRawWeight W n (upperTailLength c n) K
      (roughHeadBalancedAlpha W n (upperTailLength c n) K beta (L n))
      beta (L n)
  let X := tangentPaperExceptionalCutoff deltaStar n
  let B := X / 2
  have hnTwo : 1 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by positivity
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  have hL : 0 < L n := L_pos hnTwo
  have hlogYPos : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num : (0 : Real) < 1 / 5) hL).trans_le hlogY
  have hB : 1 ≤ B := by omega
  have hBReal : (0 : Real) < (B : Real) := by exact_mod_cast hB
  have hXReal : (0 : Real) < (X : Real) := by positivity
  have hheadNonneg : 0 ≤
      (roughHeadModulus W : Real) / roughHeadDensity W := by
    exact div_nonneg (Nat.cast_nonneg _) (roughHeadDensity_pos W).le
  have hfinite :=
    abs_roughCanonicalSignedExceptionalResidual_le_coreFirstFinite
      hdelta.le (by omega) htail hp hWp hpY hcut hdeep hcutoff hvariation hcore
  have hinvLog : 1 / Real.log (yNat n : Real) ≤ 5 / L n := by
    apply (div_le_div_iff₀ hlogYPos hL).2
    nlinarith [hlogY]
  have htailScale' :
      (upperTailLength c n : Real) ≤ 2 * c * (n : Real) / L n := by
    calc
      (upperTailLength c n : Real) ≤
          2 * c * secondOrderScale n := htailScale
      _ = 2 * c * (n : Real) / L n := by
        unfold secondOrderScale L
        ring
  have hleadingScale :
      (upperTailLength c n : Real) / Real.log (yNat n : Real) ≤
        10 * c * (n : Real) / L n ^ 2 := by
    calc
      (upperTailLength c n : Real) / Real.log (yNat n : Real) =
          (upperTailLength c n : Real) *
            (1 / Real.log (yNat n : Real)) := by ring
      _ ≤ (2 * c * (n : Real) / L n) * (5 / L n) :=
        mul_le_mul htailScale' hinvLog (by positivity) (by positivity)
      _ = 10 * c * (n : Real) / L n ^ 2 := by ring
  have hBLe : B ≤ 2 * X := by omega
  have hlogB : Real.log (B : Real) ≤ Real.log (2 * X : Nat) :=
    Real.log_le_log hBReal (by exact_mod_cast hBLe)
  have hdeepLog :
      1 + Real.log (B : Real) ≤ 2 * deltaStar * L n := by
    have hlogCut' :
        1 + Real.log ((2 * X : Nat) : Real) ≤ 2 * deltaStar * L n := by
      simpa only [X] using hlogCut
    linarith
  let baseScale := (n : Real) / ((p : Real) * L n ^ 2)
  have hbase : 0 ≤ baseScale := by
    dsimp [baseScale]
    positivity
  have hleadTerm :
      ((upperTailLength c n : Real) / Real.log (yNat n : Real)) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) ≤
        (20 * c *
          ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant) * baseScale := by
    have hfactorNonneg : 0 ≤
        2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
          variationConstant / (p : Real) := by positivity
    calc
      _ ≤ (10 * c * (n : Real) / L n ^ 2) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) :=
        mul_le_mul_of_nonneg_right hleadingScale hfactorNonneg
      _ = _ := by
        dsimp [baseScale]
        ring
  have hdeepMain :
      (deepConstant * (n : Real) / L n ^ 3) *
          (2 * (1 + Real.log (B : Real)) / (p : Real)) ≤
        (4 * deltaStar * deepConstant) * baseScale := by
    have hfirstNonneg : 0 ≤ deepConstant * (n : Real) / L n ^ 3 := by
      positivity
    have hsecond :
        2 * (1 + Real.log (B : Real)) / (p : Real) ≤
          4 * deltaStar * L n / (p : Real) := by
      have hnumerator :
          2 * (1 + Real.log (B : Real)) ≤
            4 * deltaStar * L n := by
        nlinarith [hdeepLog]
      exact div_le_div_of_nonneg_right hnumerator hpReal.le
    calc
      _ ≤ (deepConstant * (n : Real) / L n ^ 3) *
          (4 * deltaStar * L n / (p : Real)) :=
        mul_le_mul_of_nonneg_left hsecond hfirstNonneg
      _ = _ := by
        dsimp [baseScale]
        field_simp [hL.ne', hpReal.ne']
  have hdeepEndpoint :
      deepConstant * (2 * (B : Real) / (p : Real)) ≤
        (2 * deepConstant) * baseScale := by
    have hBX : (B : Real) ≤ (X : Real) := by exact_mod_cast (Nat.div_le_self X 2)
    have hBscale : (B : Real) ≤ (n : Real) / L n ^ 2 :=
      hBX.trans hendpoint
    have hscaled :
        2 * (B : Real) / (p : Real) ≤
          2 * ((n : Real) / L n ^ 2) / (p : Real) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBscale (by norm_num)) hpReal.le
    calc
      deepConstant * (2 * (B : Real) / (p : Real)) ≤
          deepConstant * (2 * ((n : Real) / L n ^ 2) / (p : Real)) := by
        exact mul_le_mul_of_nonneg_left hscaled hdeep
      _ = _ := by
        dsimp [baseScale]
        ring
  have hbandMain :
      (cutoffConstant * (n : Real) / L n ^ 2) *
          (8 / (p : Real)) =
        (8 * cutoffConstant) * baseScale := by
    dsimp [baseScale]
    ring
  have hbandEndpoint :
      cutoffConstant * (4 * (X : Real) / (p : Real)) ≤
        (4 * cutoffConstant) * baseScale := by
    have hscaled :
        4 * (X : Real) / (p : Real) ≤
          4 * ((n : Real) / L n ^ 2) / (p : Real) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hendpoint (by norm_num)) hpReal.le
    calc
      cutoffConstant * (4 * (X : Real) / (p : Real)) ≤
          cutoffConstant *
            (4 * ((n : Real) / L n ^ 2) / (p : Real)) := by
        exact mul_le_mul_of_nonneg_left hscaled hcutoff
      _ = _ := by
        dsimp [baseScale]
        ring
  have htotal :
      ((upperTailLength c n : Real) / Real.log (yNat n : Real)) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) +
        (deepConstant * (n : Real) / L n ^ 3) *
          (2 * (1 + Real.log (B : Real)) / (p : Real)) +
        deepConstant * (2 * (B : Real) / (p : Real)) +
        (cutoffConstant * (n : Real) / L n ^ 2) *
          (8 / (p : Real)) +
        cutoffConstant * (4 * (X : Real) / (p : Real)) ≤
      roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
          deepConstant cutoffConstant variationConstant * baseScale := by
    calc
      _ ≤ (20 * c *
              ((roughHeadModulus W : Real) / roughHeadDensity W) *
                variationConstant) * baseScale +
            (4 * deltaStar * deepConstant) * baseScale +
            (2 * deepConstant) * baseScale +
            (8 * cutoffConstant) * baseScale +
            (4 * cutoffConstant) * baseScale := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (add_le_add hleadTerm hdeepMain)
              hdeepEndpoint)
            (le_of_eq hbandMain))
          hbandEndpoint
      _ = roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
            deepConstant cutoffConstant variationConstant * baseScale := by
        unfold roughCanonicalSignedExceptionalCoreBoundConstant
        ring
  unfold RoughCanonicalSignedExceptionalResidualBound
  apply hfinite.trans
  calc
    _ ≤ roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
          deepConstant cutoffConstant variationConstant * baseScale := by
      simpa only [B, X] using htotal
    _ = roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
          deepConstant cutoffConstant variationConstant *
            secondOrderScale n / ((p : Real) * L n) := by
      dsimp [baseScale, secondOrderScale, L]
      field_simp [hL.ne', hpReal.ne']

end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {W K : Nat} {c deltaStar beta deepConstant cutoffConstant variationConstant : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      LT.lt.{0} deltaStar (1 / 18 : Real) →
        LE.le.{0} (0 : Real) deepConstant →
          LE.le.{0} (0 : Real) cutoffConstant →
            LE.le.{0} (0 : Real) variationConstant →
              Erdos390.WholePaper.BankPaperRealization.RoughCanonicalSignedExceptionalCoreChamberEventually W K c
                  deltaStar beta deepConstant cutoffConstant variationConstant →
                ∀ᶠ (n : Nat) in Filter.atTop.{0},
                  ∀ (p : Nat),
                    Nat.Prime p →
                      LT.lt.{0} W p →
                        LE.le.{0} p (Erdos390.Full.ArithmeticModel.yNat n) →
                          Erdos390.WholePaper.BankPaperRealization.RoughCanonicalSignedExceptionalResidualBound n
                            (Erdos390.WholePaper.upperTailLength c n) K deltaStar
                            (Erdos390.WholePaper.roughHeadCompatibleRawWeight W n
                              (Erdos390.WholePaper.upperTailLength c n) K
                              (Erdos390.WholePaper.roughHeadBalancedAlpha W n (Erdos390.WholePaper.upperTailLength c n)
                                K beta (Erdos390.Full.Scale.L n))
                              beta (Erdos390.Full.Scale.L n))
                            p
                            (HDiv.hDiv.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0}
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalCoreBoundConstant
                                  W c deltaStar deepConstant cutoffConstant variationConstant)
                                (Erdos390.WholePaper.secondOrderScale n))
                              (HMul.hMul.{0, 0, 0} (↑p) (Erdos390.Full.Scale.L n))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalSignedExceptionalResidualBound_of_coreChamber
