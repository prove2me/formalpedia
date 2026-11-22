-- Prove2me | solution 1 for Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:43:51.262084+00:00
-- url     : https://prove2.me/submissions/947ba6d2-a3e5-4c18-8e79-b9bcbffdafea

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
import Theorems.Thm_Erdos390_Full_FriableAsymptotic_exists_uniform_friableCount_dickman_bound
import Theorems.Thm_Erdos390_WholePaper_exists_uniform_roughFixedHead_friableCount_shift_bound_compact
import Theorems.Thm_Erdos390_WholePaper_roughCanonical_dickmanEndpointMain_sub_lower_compact
import Theorems.Thm_Erdos390_WholePaper_roughCanonical_headFreeSmoothInterval_lower_of_shift_compact




section
theorem Erdos390.WholePaper.roughCanonical_headFreeSmoothInterval_lower_of_shift : Erdos390.RemainingAnalyticGoal008_018 := @Erdos390.WholePaper.roughCanonical_headFreeSmoothInterval_lower_of_shift_compact
end
section
theorem Erdos390.WholePaper.roughCanonical_dickmanEndpointMain_sub_lower : Erdos390.RemainingAnalyticGoal008_017 := @Erdos390.WholePaper.roughCanonical_dickmanEndpointMain_sub_lower_compact
end
section
theorem Erdos390.WholePaper.exists_uniform_roughFixedHead_friableCount_shift_bound : Erdos390.RemainingAnalyticGoal008_013 := @Erdos390.WholePaper.exists_uniform_roughFixedHead_friableCount_shift_bound_compact
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

/- Source module: Erdos390.Full.StructuredCells -/
section


/-!
# Exact structured-cell reductions

This file defines the actual finite smooth intervals and exact head cells.
It proves the finite inclusion--exclusion identity before any use of a
friable-number asymptotic.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.StructuredCells

open HeadPattern













theorem smoothNumbersUpTo_mono {X₁ X₂ y : ℕ} (hX : X₁ ≤ X₂) :
    Nat.smoothNumbersUpTo X₁ (y + 1) ⊆
      Nat.smoothNumbersUpTo X₂ (y + 1) := by
  intro m hm
  rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans hX, hm.2⟩

/-- An exact interval count is a difference of two `psi` values. -/
theorem smoothInterval_card_eq_psi_sub {lo hi y : ℕ} (hlohi : lo ≤ hi) :
    (smoothInterval lo hi y).card = psi hi y - psi lo y := by
  have hset : smoothInterval lo hi y =
      Nat.smoothNumbersUpTo hi (y + 1) \
        Nat.smoothNumbersUpTo lo (y + 1) := by
    ext m
    simp only [mem_smoothInterval, Finset.mem_sdiff,
      Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨hlom, hmhi, hsmooth⟩
      exact ⟨⟨hmhi, hsmooth⟩, fun hlow ↦ (Nat.not_le_of_lt hlom) hlow.1⟩
    · rintro ⟨⟨hmhi, hsmooth⟩, hnotlow⟩
      refine ⟨?_, hmhi, hsmooth⟩
      by_contra hnlt
      exact hnotlow ⟨Nat.le_of_not_gt hnlt, hsmooth⟩
  rw [hset, Finset.card_sdiff]
  have hinter :
      Nat.smoothNumbersUpTo lo (y + 1) ∩
          Nat.smoothNumbersUpTo hi (y + 1) =
        Nat.smoothNumbersUpTo lo (y + 1) := by
    exact Finset.inter_eq_left.mpr (smoothNumbersUpTo_mono hlohi)
  rw [hinter]
  rfl





















end Erdos390.Full.StructuredCells

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

























theorem friableCount_mono_left {X₁ X₂ y : ℕ} (hX : X₁ ≤ X₂) :
    friableCount X₁ y ≤ friableCount X₂ y := by
  apply Finset.card_le_card
  intro m hm
  rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans hX, hm.2⟩







/-- Exact Dickman formula on the initial face `u ≤ 1`.  The only discrepancy
between the real endpoint and the count is therefore the explicit floor used
to create `X`; no analytic error occurs here. -/
theorem friableCount_eq_dickman_initial {X y : ℕ} (hX : 0 < X)
    (hy : 1 < y) (hXy : X ≤ y) :
    (friableCount X y : ℝ) = (X : ℝ) * rho (dickmanU X y) := by
  rw [friableCount_eq_self hXy, rho_eq_one_of_le_one
    (dickmanU_le_one hX hy hXy)]
  ring

















/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/
























































/-- Uniform Dickman estimate with the exact initial face included. -/
theorem exists_uniform_friableCount_dickman_bound_all_faces :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → 0 < X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(friableCount X y : ℝ) - (X : ℝ) * rho (dickmanU X y)| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₁, hmain⟩ :=
    exists_uniform_friableCount_dickman_bound
  refine ⟨K, hK, max 2 Y₁, ?_⟩
  intro X y hy hX hlog
  have hy2 : 2 ≤ y := (le_max_left 2 Y₁).trans hy
  have hY₁y : Y₁ ≤ y := (le_max_right 2 Y₁).trans hy
  by_cases hyX : y ≤ X
  · exact hmain hY₁y hyX hlog
  · have hXy : X ≤ y := le_of_not_ge hyX
    rw [friableCount_eq_dickman_initial hX (by omega) hXy,
      sub_self, abs_zero]
    positivity




end Erdos390.Full.FriableAsymptotic

end

/- Source module: Erdos390.Full.MarkedFriableAsymptotic -/
section


open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology Asymptotics

namespace Erdos390.Full.MarkedFriableAsymptotic

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern

theorem psi_eq_friableCount (X y : ℕ) :
    psi X y = FriableAsymptotic.friableCount X y := rfl





end Erdos390.Full.MarkedFriableAsymptotic

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



/-- Nonzero smooth-part coordinates lie weakly below the cutoff. -/
theorem completeSmoothPart_factorization_support
    {y a p : ℕ}
    (hp : (completeSmoothPart y a).factorization p ≠ 0) :
    p ≤ y := by
  rw [completeSmoothPart_factorization_apply] at hp
  by_contra hpLow
  simp [hpLow] at hp



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

/-- Uniqueness of the decomposition under the literal complementary
factorization-support conditions. -/
theorem completeRoughDecomposition_unique
    {y a rough smooth : ℕ}
    (hrough : rough ≠ 0) (hsmooth : smooth ≠ 0)
    (hproduct : a = rough * smooth)
    (hroughSupport : ∀ p, rough.factorization p ≠ 0 → y < p)
    (hsmoothSupport : ∀ p, smooth.factorization p ≠ 0 → p ≤ y) :
    rough = completeRoughLabel y a ∧
      smooth = completeSmoothPart y a := by
  have hfactorization :
      a.factorization = rough.factorization + smooth.factorization := by
    rw [hproduct, Nat.factorization_mul hrough hsmooth]
  have hroughEq : rough = completeRoughLabel y a := by
    apply Nat.eq_of_factorization_eq' hrough
      (completeRoughLabel_ne_zero y a)
    rw [completeRoughLabel_factorization_eq_filter_gt]
    ext p
    have hcoordinate :=
      congrArg (fun f : ℕ →₀ ℕ ↦ f p) hfactorization
    simp only [Finsupp.add_apply] at hcoordinate
    rw [Finsupp.filter_apply]
    by_cases hpHigh : y < p
    · rw [if_pos hpHigh]
      have hsmoothZero : smooth.factorization p = 0 := by
        by_contra hsmoothNonzero
        exact (Nat.not_le_of_gt hpHigh)
          (hsmoothSupport p hsmoothNonzero)
      simpa only [hsmoothZero, add_zero] using hcoordinate.symm
    · rw [if_neg hpHigh]
      by_contra hroughNonzero
      exact hpHigh (hroughSupport p hroughNonzero)
  refine ⟨hroughEq, ?_⟩
  apply Nat.mul_left_cancel (completeRoughLabel_pos y a)
  calc
    completeRoughLabel y a * smooth = rough * smooth := by
      rw [hroughEq]
    _ = a := hproduct.symm
    _ = completeRoughLabel y a * completeSmoothPart y a :=
      completeRough_decomposition y a





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasCanonicalRowBridge -/
section


/-!
# Canonical-row consumer for the weighted Saias block

The analytic four-endpoint expression is useful to the construction only
after it is tied back to the literal complete-rough row used by floating
rounding.  This file supplies that consumer-facing bridge.  The sum over a
canonical `rowSet` is identified unconditionally with the already-defined
literal raw row mass.  The upper quota minus that mass is then connected to
`roughPhysicalFriableCombination` and hence to the weighted Saias bound.

The upper endpoint identification is an exact equality.  Finite head
inclusion--exclusion and the fixed-head physical shift occur between the
literal raw mass and the density-scaled four-endpoint block in the paper,
so their error is retained as a separate explicit allowance.  It is not
silently folded into the HT--Saias hypothesis.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section









/-- Multiplying an intrinsic complete-rough label by a positive smooth
integer leaves that complete rough label unchanged. -/
theorem completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth
    {y label s : ℕ}
    (hlabel : IsCompleteRoughLabel y label)
    (hs : s ∈ Nat.smoothNumbers (y + 1)) :
    completeRoughLabel y (label * s) = label := by
  have hsPos : 0 < s :=
    (Nat.mem_smoothNumbers.mp hs).1.bot_lt
  have hsSupport : ∀ p, s.factorization p ≠ 0 → p ≤ y := by
    intro p hp
    have hpPrime : p.Prime := by
      by_contra hnotPrime
      rw [Nat.factorization_eq_zero_of_not_prime s hnotPrime] at hp
      exact hp rfl
    have hpDvd : p ∣ s := Nat.dvd_of_factorization_pos hp
    have hpLt := (Nat.mem_smoothNumbers').mp hs p hpPrime hpDvd
    omega
  have hunique := completeRoughDecomposition_unique
    (y := y) (a := label * s) (rough := label) (smooth := s)
      hlabel.1.ne' hsPos.ne' rfl hlabel.2 hsSupport
  exact hunique.1.symm





/-- Head-free version of the exact row-to-smooth-quotient reindexing. -/
theorem completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
    {W lo hi y label : ℕ}
    (hlabel : IsCompleteRoughLabel y label)
    (hcop : Nat.Coprime label (roughHeadModulus W)) :
    (completeRoughRowFiber y
        (roughHeadFree W (Finset.Ioc lo hi)) label).card =
      (roughHeadFreeSmoothInterval W (lo / label) (hi / label) y).card := by
  apply Finset.card_bij (fun a _ha ↦ a / label)
  · intro a ha
    rw [mem_completeRoughRowFiber] at ha
    have haHead := mem_roughHeadFree.mp ha.1
    have haInterval := Finset.mem_Ioc.mp haHead.1
    have hdvd : label ∣ a := by
      rw [← ha.2]
      exact completeRoughLabel_dvd y a
    apply mem_roughHeadFree.mpr
    constructor
    · apply Erdos390.Full.StructuredCells.mem_smoothInterval.mpr
      constructor
      · apply (Nat.div_lt_iff_lt_mul hlabel.1).mpr
        simpa [Nat.div_mul_cancel hdvd] using haInterval.1
      · constructor
        · apply (Nat.le_div_iff_mul_le hlabel.1).mpr
          simpa [Nat.div_mul_cancel hdvd] using haInterval.2
        · have haPos : 0 < a := Nat.zero_lt_of_lt haInterval.1
          simpa only [completeSmoothPart, ha.2] using
            completeSmoothPart_mem_smoothNumbers (y := y) haPos
    · rw [← Nat.div_mul_cancel hdvd] at haHead
      exact (Nat.coprime_mul_iff_left.mp haHead.2).1
  · intro a₁ ha₁ a₂ ha₂ heq
    rw [mem_completeRoughRowFiber] at ha₁ ha₂
    have hdvd₁ : label ∣ a₁ := by
      rw [← ha₁.2]
      exact completeRoughLabel_dvd y a₁
    have hdvd₂ : label ∣ a₂ := by
      rw [← ha₂.2]
      exact completeRoughLabel_dvd y a₂
    calc
      a₁ = a₁ / label * label := (Nat.div_mul_cancel hdvd₁).symm
      _ = a₂ / label * label := by rw [heq]
      _ = a₂ := Nat.div_mul_cancel hdvd₂
  · intro s hs
    have hsHead := mem_roughHeadFree.mp hs
    have hsData :=
      Erdos390.Full.StructuredCells.mem_smoothInterval.mp hsHead.1
    refine ⟨label * s, ?_, ?_⟩
    · apply mem_completeRoughRowFiber.mpr
      constructor
      · apply mem_roughHeadFree.mpr
        constructor
        · apply Finset.mem_Ioc.mpr
          constructor
          · have hlo := (Nat.div_lt_iff_lt_mul hlabel.1).mp hsData.1
            simpa only [Nat.mul_comm] using hlo
          · have hhi := (Nat.le_div_iff_mul_le hlabel.1).mp hsData.2.1
            simpa only [Nat.mul_comm] using hhi
        · exact Nat.coprime_mul_iff_left.mpr ⟨hcop, hsHead.2⟩
      · exact completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth
          hlabel hsData.2.2
    · simpa only [Nat.mul_comm] using Nat.mul_div_left s hlabel.1

































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











/-- Label one is intrinsically a complete-rough label at every cutoff. -/
theorem isCompleteRoughLabel_one (y : Nat) :
    IsCompleteRoughLabel y 1 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp
  simp at hp

/-- Exact reindexing of the label-one base pool as the head-free smooth
interval used in the paper's displayed mass formula. -/
theorem bankPaperCanonicalRawSmoothBasePool_card_eq_headFreeSmoothInterval
    (W n h K : Nat) :
    (bankPaperCanonicalRawSmoothBasePool W n h K).card =
      (roughHeadFreeSmoothInterval W n (2 * n - K * h) (yNat n)).card := by
  unfold bankPaperCanonicalRawSmoothBasePool
  unfold roughCanonicalBroadCorrectionPool roughBroadLowerBlock
  simpa using
    (completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
      (W := W) (lo := n) (hi := 2 * n - K * h)
      (y := yNat n) (label := 1)
      (isCompleteRoughLabel_one (yNat n)) (by simp))



/-! ## Tie-lower nearest integers -/











/-! ## Exact smooth-row quota initialization -/



























/-! ## Exact frozen-height ledger and centered adjustment -/



























/-! ## Literal Section 8 families -/

























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



/-- The fixed Dickman floor is strictly positive. -/
theorem roughCanonicalPoolDickmanFloor_pos :
    0 < roughCanonicalPoolDickmanFloor := by
  unfold roughCanonicalPoolDickmanFloor
  exact rho_pos_on_zero_five (by norm_num) le_rfl



/-! ## Growth of the unrestricted smooth interval -/



/-- A supplied uniform de Bruijn estimate gives a fixed positive lower
bound for a smooth interval whose length is a fixed fraction of its lower
endpoint. -/
theorem roughCanonical_smoothInterval_card_lower
    {C : Real} {Y0 A B y : Nat}
    (hC : 0 < C)
    (hdeBruijn : forall {X z : Nat},
      Y0 <= z -> 0 < X ->
      Real.log (X : Real) <= 5 * Real.log (z : Real) ->
      |(FriableAsymptotic.friableCount X z : Real) -
          (X : Real) * rho (FriableAsymptotic.dickmanU X z)| <=
        C * (X : Real) / Real.log (z : Real))
    (hY : Y0 <= y) (hyTwo : 2 <= y)
    (hA : 0 < A) (hAB : A <= B) (hBthree : B <= 3 * A)
    (hlength : A <= 2 * (B - A))
    (hlogB : Real.log (B : Real) <= 5 * Real.log (y : Real))
    (hlogMain :
      2 / Real.log (y : Real) <= roughCanonicalPoolDickmanFloor)
    (hlogError :
      8 * C / Real.log (y : Real) <=
        roughCanonicalPoolDickmanFloor / 4) :
    roughCanonicalPoolDickmanFloor / 8 * (A : Real) <=
      ((smoothInterval A B y).card : Real) := by
  have hBPos : 0 < B := hA.trans_le hAB
  have hyReal : (1 : Real) < y := by exact_mod_cast (by omega : 1 < y)
  have hlogY : 0 < Real.log (y : Real) := Real.log_pos hyReal
  have hlogA : Real.log (A : Real) <= 5 * Real.log (y : Real) := by
    have hmono : Real.log (A : Real) <= Real.log (B : Real) := by
      apply Real.log_le_log
      · exact_mod_cast hA
      · exact_mod_cast hAB
    exact hmono.trans hlogB
  have hPsiA := hdeBruijn hY hA hlogA
  have hPsiB := hdeBruijn hY hBPos hlogB
  have hmain := roughCanonical_dickmanEndpointMain_sub_lower
    hyTwo hA hAB hlogB hlogMain
  have hlengthReal :
      (A : Real) <= 2 * ((B : Real) - (A : Real)) := by
    have hlengthCast :
        (A : Real) <= 2 * (((B - A : Nat) : Real)) := by
      exact_mod_cast hlength
    simpa only [Nat.cast_sub hAB] using hlengthCast
  have hsumEndpoints :
      (A : Real) + (B : Real) <=
        8 * ((B : Real) - (A : Real)) := by
    have hBthreeReal : (B : Real) <= 3 * (A : Real) := by
      exact_mod_cast hBthree
    linarith
  have herror :
      C * (B : Real) / Real.log (y : Real) +
          C * (A : Real) / Real.log (y : Real) <=
        roughCanonicalPoolDickmanFloor / 4 *
          ((B : Real) - (A : Real)) := by
    calc
      C * (B : Real) / Real.log (y : Real) +
          C * (A : Real) / Real.log (y : Real) =
        C * ((A : Real) + (B : Real)) /
          Real.log (y : Real) := by ring
      _ <= C * (8 * ((B : Real) - (A : Real))) /
          Real.log (y : Real) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsumEndpoints hC.le) hlogY.le
      _ = (8 * C / Real.log (y : Real)) *
          ((B : Real) - (A : Real)) := by ring
      _ <= roughCanonicalPoolDickmanFloor / 4 *
          ((B : Real) - (A : Real)) := by
        apply mul_le_mul_of_nonneg_right hlogError
        exact sub_nonneg.mpr (by exact_mod_cast hAB)
  have hPsiLower :
      roughCanonicalPoolDickmanFloor / 4 *
          ((B : Real) - (A : Real)) <=
        (FriableAsymptotic.friableCount B y : Real) -
          (FriableAsymptotic.friableCount A y : Real) := by
    have hlowerB := (abs_le.mp hPsiB).1
    have hupperA := (abs_le.mp hPsiA).2
    have hmain' :
        roughCanonicalPoolDickmanFloor / 2 *
            ((B : Real) - (A : Real)) <=
          (B : Real) * rho (FriableAsymptotic.dickmanU B y) -
            (A : Real) * rho (FriableAsymptotic.dickmanU A y) := by
      simpa only [Nat.cast_sub hAB] using hmain
    linarith
  have hmono := FriableAsymptotic.friableCount_mono_left (y := y) hAB
  rw [smoothInterval_card_eq_psi_sub hAB]
  simp_rw [Erdos390.Full.MarkedFriableAsymptotic.psi_eq_friableCount]
  rw [Nat.cast_sub hmono]
  calc
    roughCanonicalPoolDickmanFloor / 8 * (A : Real) <=
        roughCanonicalPoolDickmanFloor / 4 *
          ((B : Real) - (A : Real)) := by
      have hfloorNonneg := roughCanonicalPoolDickmanFloor_pos.le
      have hscaled :=
        mul_le_mul_of_nonneg_left hlengthReal hfloorNonneg
      nlinarith
    _ <= _ := hPsiLower

/-! ## Closing the fixed head -/







/-- Once the logarithmic and fixed endpoint losses are small, the
head-free smooth interval retains a fixed linear fraction of its lower
endpoint. -/
theorem roughCanonical_headFreeSmoothInterval_card_lower
    {W : Nat} {C Kshift : Real} {YdeBruijn Yshift A B y : Nat}
    (hC : 0 < C) (hKshift : 0 < Kshift)
    (hdeBruijn : forall {X z : Nat},
      YdeBruijn <= z -> 0 < X ->
      Real.log (X : Real) <= 5 * Real.log (z : Real) ->
      |(FriableAsymptotic.friableCount X z : Real) -
          (X : Real) * rho (FriableAsymptotic.dickmanU X z)| <=
        C * (X : Real) / Real.log (z : Real))
    (hshift : forall {X z d : Nat},
      Yshift <= z ->
      d ∈ (roughHeadModulus W).divisors -> d <= X ->
      Real.log (X : Real) <= 5 * Real.log (z : Real) ->
      |(FriableAsymptotic.friableCount (X / d) z : Real) -
          (FriableAsymptotic.friableCount X z : Real) / (d : Real)| <=
        Kshift * (X : Real) /
            ((d : Real) * Real.log (z : Real)) + 3)
    (hYdeBruijn : YdeBruijn <= y) (hYshift : Yshift <= y)
    (hWy : W <= y) (hyTwo : 2 <= y)
    (hmodA : roughHeadModulus W <= A)
    (hAB : A <= B) (hBthree : B <= 3 * A)
    (hlength : A <= 2 * (B - A))
    (hlogB : Real.log (B : Real) <= 5 * Real.log (y : Real))
    (hlogMain :
      2 / Real.log (y : Real) <= roughCanonicalPoolDickmanFloor)
    (hlogSmooth :
      8 * C / Real.log (y : Real) <=
        roughCanonicalPoolDickmanFloor / 4)
    (hlogHead :
      4 * (roughHeadModulus W : Real) * Kshift /
          Real.log (y : Real) <=
        roughHeadDensity W * roughCanonicalPoolDickmanFloor / 32)
    (hendpoint :
      6 * (roughHeadModulus W : Real) <=
        roughHeadDensity W * roughCanonicalPoolDickmanFloor / 32 *
          (A : Real)) :
    roughHeadDensity W * roughCanonicalPoolDickmanFloor / 16 *
        (A : Real) <=
      ((roughHeadFreeSmoothInterval W A B y).card : Real) := by
  have hA : 0 < A :=
    (roughHeadModulus_pos W).trans_le hmodA
  have hsmooth := roughCanonical_smoothInterval_card_lower
    hC hdeBruijn hYdeBruijn hyTwo hA hAB hBthree hlength hlogB
      hlogMain hlogSmooth
  have hhead := roughCanonical_headFreeSmoothInterval_lower_of_shift
    hKshift hshift hYshift hWy hyTwo hmodA hAB hlogB
  have hAplusB : (A : Real) + (B : Real) <= 4 * (A : Real) := by
    have hBthreeReal : (B : Real) <= 3 * (A : Real) := by
      exact_mod_cast hBthree
    linarith
  have hlogY : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hshiftError :
      (roughHeadModulus W : Real) *
          (Kshift * ((A : Real) + (B : Real)) /
              Real.log (y : Real) + 6) <=
        roughHeadDensity W * roughCanonicalPoolDickmanFloor / 16 *
          (A : Real) := by
    calc
      _ = (roughHeadModulus W : Real) * Kshift *
            ((A : Real) + (B : Real)) /
              Real.log (y : Real) +
          6 * (roughHeadModulus W : Real) := by ring
      _ <= (roughHeadModulus W : Real) * Kshift *
            (4 * (A : Real)) / Real.log (y : Real) +
          6 * (roughHeadModulus W : Real) := by
        gcongr
      _ = (4 * (roughHeadModulus W : Real) * Kshift /
            Real.log (y : Real)) * (A : Real) +
          6 * (roughHeadModulus W : Real) := by ring
      _ <= (roughHeadDensity W * roughCanonicalPoolDickmanFloor / 32) *
            (A : Real) +
          (roughHeadDensity W * roughCanonicalPoolDickmanFloor / 32) *
            (A : Real) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hlogHead (Nat.cast_nonneg A))
          hendpoint
      _ = roughHeadDensity W * roughCanonicalPoolDickmanFloor / 16 *
          (A : Real) := by ring
  have hmain :
      roughHeadDensity W * roughCanonicalPoolDickmanFloor / 8 *
          (A : Real) <=
        roughHeadDensity W * ((smoothInterval A B y).card : Real) := by
    calc
      _ = roughHeadDensity W *
          (roughCanonicalPoolDickmanFloor / 8 * (A : Real)) := by ring
      _ <= roughHeadDensity W *
          ((smoothInterval A B y).card : Real) :=
        mul_le_mul_of_nonneg_left hsmooth (roughHeadDensity_pos W).le
  linarith

/-! ## Literal rough-row adapters -/













/-! ## Uniform paper-scale choices -/























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

private theorem bankPaperCanonicalSmoothBase_yNat_tendsto_atTop :
    Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : Nat => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : Real) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

private theorem bankPaperCanonicalSmoothBase_log_yNat_tendsto_atTop :
    Tendsto (fun n : Nat => Real.log (yNat n : Real)) atTop atTop := by
  have hyReal : Tendsto (fun n : Nat => (yNat n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      bankPaperCanonicalSmoothBase_yNat_tendsto_atTop
  exact Real.tendsto_log_atTop.comp hyReal

/-- The explicit label-one head-free broad pool retains a fixed positive
linear fraction of `n`.  Unlike the existing active-row theorem, this result
does not exclude label one. -/
theorem eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower
    (W K : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      roughCanonicalRawBroadPoolDensity W * (n : Real) <=
        ((bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) := by
  obtain ⟨C, hC, YdeBruijn, hdeBruijn⟩ :=
    FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces
  obtain ⟨Kshift, hKshift, Yshift, hshift⟩ :=
    exists_uniform_roughFixedHead_friableCount_shift_bound W
  let P : Real := roughHeadModulus W
  let r : Real := roughCanonicalPoolDickmanFloor
  have hr : 0 < r := by
    dsimp only [r]
    exact roughCanonicalPoolDickmanFloor_pos
  let A0 : Nat :=
    max (roughHeadModulus W)
      (max 2 ⌈192 * P / (roughHeadDensity W * r)⌉₊)
  let logThreshold : Real :=
    max (2 / r)
      (max (32 * C / r)
        (128 * P * Kshift / (roughHeadDensity W * r)))
  have hlogEvent : ∀ᶠ n : Nat in atTop,
      logThreshold <= Real.log (yNat n : Real) :=
    bankPaperCanonicalSmoothBase_log_yNat_tendsto_atTop.eventually
      (eventually_ge_atTop logThreshold)
  have hyEvent : ∀ᶠ n : Nat in atTop,
      max W (max YdeBruijn (max Yshift 2)) <= yNat n :=
    bankPaperCanonicalSmoothBase_yNat_tendsto_atTop.eventually
      (eventually_ge_atTop (max W (max YdeBruijn (max Yshift 2))))
  have hAEvent : ∀ᶠ n : Nat in atTop, A0 <= n :=
    eventually_ge_atTop A0
  have htailEvent : ∀ᶠ n : Nat in atTop,
      ((2 * K * upperTailLength c n : Nat) : Real) / (n : Real) <=
        1 / 2 := by
    have hT : Tendsto
        (fun n : Nat => (2 * (K : Real)) *
          ((upperTailLength c n : Real) / (n : Real)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        (upperTailLength_ratio_tendsto_zero hc).const_mul
          (2 * (K : Real))
    have hsmall := hT.eventually
      (eventually_lt_nhds (by norm_num : (0 : Real) < 1 / 2))
    filter_upwards [hsmall] with n hn
    have hn' :
        (2 * (K : Real)) *
            ((upperTailLength c n : Real) / (n : Real)) < 1 / 2 := hn
    calc
      ((2 * K * upperTailLength c n : Nat) : Real) / (n : Real) =
          (2 * (K : Real)) *
            ((upperTailLength c n : Real) / (n : Real)) := by
        push_cast
        ring
      _ <= 1 / 2 := hn'.le
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLEvent : ∀ᶠ n : Nat in atTop,
      54 * Real.log 2 <= L n :=
    hLTop.eventually (eventually_ge_atTop (54 * Real.log 2))
  filter_upwards [eventually_gt_atTop 0, hlogEvent, hyEvent, hAEvent,
    htailEvent, hLEvent] with n hn hlog hy hA0 htail hLlarge
  let A : Nat := n
  let B : Nat := 2 * n - K * upperTailLength c n
  have htailNat : 4 * K * upperTailLength c n <= n := by
    have hnReal : (0 : Real) < n := by exact_mod_cast hn
    have hcross := (div_le_iff₀ hnReal).mp htail
    have hcast :
        ((2 * K * upperTailLength c n : Nat) : Real) <=
          (n : Real) / 2 := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hcross
    have hcast' :
        ((4 * K * upperTailLength c n : Nat) : Real) <= (n : Real) := by
      push_cast at hcast ⊢
      linarith
    exact_mod_cast hcast'
  have htailNat' :
      4 * (K * upperTailLength c n) <= n := by
    simpa only [mul_assoc] using htailNat
  have hKh : K * upperTailLength c n <= n := by omega
  have hAB : A <= B := by
    dsimp only [A, B]
    omega
  have hBthree : B <= 3 * A := by
    dsimp only [A, B]
    omega
  have hlength : A <= 2 * (B - A) := by
    dsimp only [A, B]
    omega
  have hmodA : roughHeadModulus W <= A := by
    dsimp only [A]
    exact (le_max_left _ _).trans hA0
  have hyTwo : 2 <= yNat n :=
    (le_max_right Yshift 2).trans
      ((le_max_right YdeBruijn _).trans ((le_max_right W _).trans hy))
  have hlogB : Real.log (B : Real) <=
      5 * Real.log (yNat n : Real) := by
    have hAPos : 0 < A := by simpa only [A] using hn
    have hBPos : 0 < B := hAPos.trans_le hAB
    have hBLe : B <= 2 * n := by
      dsimp only [B]
      exact Nat.sub_le _ _
    have hlogLe : Real.log (B : Real) <=
        Real.log ((2 * n : Nat) : Real) :=
      Real.log_le_log (by exact_mod_cast hBPos) (by exact_mod_cast hBLe)
    have hypos : 0 < y n := y_pos hn
    have hyFloor : (yNat n : Real) <= y n := Nat.floor_le hypos.le
    have hyRealTwo : (2 : Real) <= y n := by
      exact (by exact_mod_cast hyTwo : (2 : Real) <= (yNat n : Real)).trans
        hyFloor
    have hyNatLower : y n / 2 <= (yNat n : Real) := by
      have hfloor : y n < (yNat n : Real) + 1 := Nat.lt_floor_add_one _
      linarith
    have hlogLower : Real.log (y n / 2) <=
        Real.log (yNat n : Real) :=
      Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
    have hlogDiv : Real.log (y n / 2) =
        Real.log (y n) - Real.log 2 := by
      rw [Real.log_div hypos.ne' (by norm_num : (2 : Real) ≠ 0)]
    calc
      Real.log (B : Real) <= Real.log ((2 * n : Nat) : Real) := hlogLe
      _ = Real.log 2 + L n := by
        rw [show ((2 * n : Nat) : Real) = 2 * (n : Real) by norm_num,
          Real.log_mul (by norm_num : (2 : Real) ≠ 0)
            (by exact_mod_cast hn.ne')]
        rfl
      _ <= 5 * Real.log (y n / 2) := by
        rw [hlogDiv, log_y hn]
        nlinarith
      _ <= 5 * Real.log (yNat n : Real) := by
        gcongr
  have hlogY : 0 < Real.log (yNat n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hlogMain :
      2 / Real.log (yNat n : Real) <= r := by
    have hthreshold : 2 / r <= Real.log (yNat n : Real) :=
      (le_max_left _ _).trans hlog
    exact (div_le_iff₀ hlogY).2 <| by
      simpa only [mul_comm] using (div_le_iff₀ hr).1 hthreshold
  have hlogSmooth :
      8 * C / Real.log (yNat n : Real) <= r / 4 := by
    have hthreshold : 32 * C / r <= Real.log (yNat n : Real) :=
      (le_max_left (32 * C / r)
        (128 * P * Kshift / (roughHeadDensity W * r))).trans
          ((le_max_right (2 / r) _).trans hlog)
    have hcross : 32 * C <=
        r * Real.log (yNat n : Real) := by
      simpa only [mul_comm] using (div_le_iff₀ hr).1 hthreshold
    have hleft : 32 * C / Real.log (yNat n : Real) <= r :=
      (div_le_iff₀ hlogY).2 hcross
    calc
      8 * C / Real.log (yNat n : Real) =
          (32 * C / Real.log (yNat n : Real)) / 4 := by ring
      _ <= r / 4 :=
        div_le_div_of_nonneg_right hleft (by norm_num)
  have hlogHead :
      4 * P * Kshift / Real.log (yNat n : Real) <=
        roughHeadDensity W * r / 32 := by
    have hthreshold :
        128 * P * Kshift / (roughHeadDensity W * r) <=
          Real.log (yNat n : Real) :=
      (le_max_right (32 * C / r) _).trans
        ((le_max_right (2 / r) _).trans hlog)
    have hdenom : 0 < roughHeadDensity W * r :=
      mul_pos (roughHeadDensity_pos W) hr
    have hnumerator : 128 * P * Kshift <=
        (roughHeadDensity W * r) * Real.log (yNat n : Real) := by
      simpa only [mul_comm] using (div_le_iff₀ hdenom).1 hthreshold
    have hcross :
        128 * P * Kshift / Real.log (yNat n : Real) <=
          roughHeadDensity W * r :=
      (div_le_iff₀ hlogY).2 hnumerator
    calc
      4 * P * Kshift / Real.log (yNat n : Real) =
          (128 * P * Kshift / Real.log (yNat n : Real)) / 32 := by ring
      _ <= (roughHeadDensity W * r) / 32 :=
        div_le_div_of_nonneg_right hcross (by norm_num)
  have hendpoint :
      6 * P <= roughHeadDensity W * r / 32 * (A : Real) := by
    have hceil :
        192 * P / (roughHeadDensity W * r) <=
          (⌈192 * P / (roughHeadDensity W * r)⌉₊ : Real) :=
      Nat.le_ceil _
    have hceilA :
        (⌈192 * P / (roughHeadDensity W * r)⌉₊ : Nat) <= A :=
      by
        have hceilA0 :
            (⌈192 * P / (roughHeadDensity W * r)⌉₊ : Nat) <= A0 :=
          (le_max_right 2 _).trans
            (le_max_right (roughHeadModulus W) _)
        simpa only [A] using hceilA0.trans hA0
    have hcastA :
        192 * P / (roughHeadDensity W * r) <= (A : Real) :=
      hceil.trans (by exact_mod_cast hceilA)
    have hdenom : 0 < roughHeadDensity W * r :=
      mul_pos (roughHeadDensity_pos W) hr
    have hcross :
        192 * P <= (A : Real) * (roughHeadDensity W * r) :=
      (div_le_iff₀ hdenom).1 hcastA
    calc
      6 * P = (192 * P) / 32 := by ring
      _ <= ((A : Real) * (roughHeadDensity W * r)) / 32 :=
        div_le_div_of_nonneg_right hcross (by norm_num)
      _ = roughHeadDensity W * r / 32 * (A : Real) := by ring
  have hlower := roughCanonical_headFreeSmoothInterval_card_lower
    hC hKshift hdeBruijn hshift
    ((le_max_left YdeBruijn (max Yshift 2)).trans
      ((le_max_right W _).trans hy))
    ((le_max_left Yshift 2).trans
      ((le_max_right YdeBruijn _).trans ((le_max_right W _).trans hy)))
    ((le_max_left W _).trans hy)
    hyTwo hmodA hAB hBthree hlength hlogB
    (by simpa only [r] using hlogMain)
    (by simpa only [r] using hlogSmooth)
    (by simpa only [P, r] using hlogHead)
    (by simpa only [P, r] using hendpoint)
  rw [bankPaperCanonicalRawSmoothBasePool_card_eq_headFreeSmoothInterval]
  simpa only [roughCanonicalRawBroadPoolDensity, A, B] using hlower





/-! ## The exact missing analytic ledger -/



/-! ## Nearest-integer initialization preserves the paper scale -/











/-! ## The logarithmically smaller height adjustment -/







/-! ## Full propagation from the minimal missing ledger -/















end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_004 := by
  exact @Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower
