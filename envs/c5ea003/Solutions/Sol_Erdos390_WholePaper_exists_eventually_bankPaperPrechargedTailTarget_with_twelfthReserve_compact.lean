-- Prove2me | solution 1 for Erdos390.WholePaper.exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:43:51.454302+00:00
-- url     : https://prove2.me/submissions/60d94e69-7c9b-4ac0-b6f7-9af93c258962

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
import Theorems.Thm_Erdos390_WholePaper_bankBottomOrientedMarkerGap_normalized_tendsto
import Theorems.Thm_Erdos390_WholePaper_exists_eventually_bankOrdinary_markerCount_lower
import Theorems.Thm_Erdos390_WholePaper_exists_eventually_centralAnchorCertificate_compact
import Theorems.Thm_Erdos390_WholePaper_guardedCentralAnchorCertificate_of_changeCost


section
theorem Erdos390.WholePaper.exists_eventually_centralAnchorCertificate : Erdos390.RemainingAnalyticGoal008_012 := @Erdos390.WholePaper.exists_eventually_centralAnchorCertificate_compact
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

/- Source module: Erdos390.WholePaper.Complement -/
section


/-!
# Exact complement formulation

This proves the complement lemma immediately following the main theorem in
the paper.  All divisions occur in `ℚ`; the proof also exports the integral
cross-multiplication form used by later valuation arguments.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section





/-- Product of every integer in `(n,M]`, without truncated division. -/
theorem factorInterval_prod_mul_factorial {n M : ℕ} (hnM : n ≤ M) :
    (factorInterval n M).prod id * n.factorial = M.factorial := by
  induction M, hnM using Nat.le_induction with
  | base => simp [factorInterval]
  | succ M hnM ih =>
      rw [factorInterval, Finset.prod_Ioc_succ_top hnM, Nat.factorial_succ]
      change ((Finset.Ioc n M).prod id * (M + 1)) * n.factorial =
        (M + 1) * M.factorial
      calc
        ((Finset.Ioc n M).prod id * (M + 1)) * n.factorial =
            (M + 1) * ((Finset.Ioc n M).prod id * n.factorial) := by
              ac_rfl
        _ = (M + 1) * M.factorial := by
          rw [show (Finset.Ioc n M).prod id * n.factorial = M.factorial by
            simpa [factorInterval] using ih]







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.PrimeLayers -/
section


/-!
# Exact prime-layer arithmetic for the lower bound

This file contains only finite identities.  Analytic estimates for the
cardinalities of the layers are kept separate.  Cross-multiplied endpoint
conditions avoid all ambiguity from natural-number division at rational
endpoints.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section











/-- Above the square-root cutoff, Legendre's sum has only its first term. -/
theorem factorial_factorization_eq_div_of_lt_sq {m p : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmSq : m < p ^ 2) :
    m.factorial.factorization p = m / p := by
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow hm.ne' hmSq)]
  simp





end

end Erdos390.WholePaper

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

/- Source module: Erdos390.WholePaper.CentralExtension -/
section


/-!
# Extension to the central binomial endpoint

This is the exact preliminary construction in the first lower-bound lemma:
a complement representation ending at `M ≤ 2n` is extended by every integer
in `(M,2n]`, producing a distinct-factor representation of `choose (2n) n`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section









theorem centralChoose_mul_factorial_sq (n : ℕ) :
    Nat.choose (2 * n) n * n.factorial ^ 2 = (2 * n).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  have hsub : 2 * n - n = n := by omega
  simpa [hsub, pow_two, mul_assoc] using h







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TailValuationCore -/
section


/-! # Per-prime factorial-tail valuation estimates -/

namespace Erdos390.WholePaper

noncomputable section

theorem factorialValuation_eq_choose_add_factorialValuation_add
    {a h p : ℕ} :
    (a + h).factorial.factorization p =
      (Nat.choose (a + h) h).factorization p +
        h.factorial.factorization p + a.factorial.factorization p := by
  have hchoosePos : 0 < Nat.choose (a + h) h :=
    Nat.choose_pos (Nat.le_add_left h a)
  have hfactorization := congrArg Nat.factorization
    (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left h a))
  simp only [Nat.add_sub_cancel_right] at hfactorization
  rw [Nat.factorization_mul
      (mul_ne_zero hchoosePos.ne' (Nat.factorial_ne_zero h))
      (Nat.factorial_ne_zero a),
    Nat.factorization_mul hchoosePos.ne' (Nat.factorial_ne_zero h)] at hfactorization
  have hcoordinate := congrArg (fun v : ℕ →₀ ℕ ↦ v p) hfactorization
  simpa only [Finsupp.add_apply] using hcoordinate.symm

theorem factorialValuationSub_eq_choose_add_factorialValuation
    {a h p : ℕ} :
    (a + h).factorial.factorization p - a.factorial.factorization p =
      (Nat.choose (a + h) h).factorization p + h.factorial.factorization p := by
  rw [factorialValuation_eq_choose_add_factorialValuation_add]
  omega



theorem centralFactorialValuation_eq_choose_add {n p : ℕ} :
    (2 * n).factorial.factorization p =
      (Nat.choose (2 * n) n).factorization p +
        2 * n.factorial.factorization p := by
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  have hfactorization := congrArg Nat.factorization
    (centralChoose_mul_factorial_sq n)
  rw [Nat.factorization_mul hchoosePos.ne'
      (pow_ne_zero 2 (Nat.factorial_ne_zero n)),
    Nat.factorization_pow] at hfactorization
  have hcoordinate := congrArg (fun v : ℕ →₀ ℕ ↦ v p) hfactorization
  simpa only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    Nat.cast_ofNat] using hcoordinate.symm







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

/- Source module: Erdos390.WholePaper.LargeCentralPrimeRouting -/
section


/-!
# Routing every large central prime to a carry row or row zero

Above a square-root cutoff, Legendre's formula has only its first term.
Thus every large prime divisor of the central binomial coefficient occurs
once, and its quotient row `n / p` determines its unique anchor family.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- If a prime occurs in the central binomial coefficient and `p^2 > 2n`,
then its valuation is one and the two floor quotients differ by one carry. -/
theorem centralChoose_largePrime_carry
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpExponent : 0 < (Nat.choose (2 * n) n).factorization p)
    (hpSq : 2 * n < p ^ 2) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      (2 * n) / p = 2 * (n / p) + 1 := by
  let r := n / p
  have hnSq : n < p ^ 2 := by omega
  have hnFac : n.factorial.factorization p = r := by
    simpa only [r] using
      factorial_factorization_eq_div_of_lt_sq hp hn hnSq
  have htwoFac : (2 * n).factorial.factorization p = (2 * n) / p := by
    exact factorial_factorization_eq_div_of_lt_sq hp (by omega) hpSq
  have hnUpper : n < p * (r + 1) := by
    simpa only [r] using Nat.lt_mul_div_succ n hp.pos
  have htwoUpper : 2 * n < (2 * r + 2) * p := by
    calc
      2 * n < 2 * (p * (r + 1)) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
      _ = (2 * r + 2) * p := by ring
  have hdivUpper : (2 * n) / p ≤ 2 * r + 1 := by
    have hlt : (2 * n) / p < 2 * r + 2 :=
      (Nat.div_lt_iff_lt_mul hp.pos).2 htwoUpper
    omega
  have hcentral := centralFactorialValuation_eq_choose_add
    (n := n) (p := p)
  rw [hnFac, htwoFac] at hcentral
  constructor <;> omega

/-- A cutoff strictly below `p` transfers its square bound to `p`. -/
theorem two_mul_lt_prime_sq_of_cutoff
    {n X p : ℕ} (hXsq : 2 * n < X ^ 2) (hXp : X < p) :
    2 * n < p ^ 2 := by
  have hPow : X ^ 2 < p ^ 2 := by
    rw [pow_two, pow_two]
    exact (Nat.mul_le_mul_left X hXp.le).trans_lt
      ((Nat.mul_lt_mul_right (by omega : 0 < p)).2 hXp)
  exact hXsq.trans hPow

/-- Every large central prime is routed exactly either to the row-zero
interval `(n,2n]` or to its positive stationary carry row. -/
theorem largeCentralPrime_rowZero_or_stationary
    {n X p : ℕ} (hn : 0 < n) (hXsq : 2 * n < X ^ 2)
    (hpMem : p ∈ largeCentralPrimes n X) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      ((n < p ∧ p ≤ 2 * n) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r) := by
  have hpPrime := largeCentralPrimes_prime hpMem
  have hpFactors : p ∈ (Nat.choose (2 * n) n).primeFactors :=
    (Finset.mem_filter.mp hpMem).1
  have hpExponent : 0 < (Nat.choose (2 * n) n).factorization p := by
    exact hpPrime.factorization_pos_of_dvd
      (Nat.choose_pos (by omega)).ne'
      (Nat.dvd_of_mem_primeFactors hpFactors)
  have hpSq := two_mul_lt_prime_sq_of_cutoff hXsq
    (largeCentralPrimes_gt hpMem)
  obtain ⟨hpOne, hfloor⟩ :=
    centralChoose_largePrime_carry hn hpPrime hpExponent hpSq
  refine ⟨hpOne, ?_⟩
  let r := n / p
  have hnUpper : n < p * (r + 1) := by
    simpa only [r] using Nat.lt_mul_div_succ n hpPrime.pos
  by_cases hrZero : r = 0
  · left
    constructor
    · simpa only [hrZero, zero_add, mul_one] using hnUpper
    · have hOneLe : 1 ≤ (2 * n) / p := by
        rw [hfloor]
        omega
      have hpLe := (Nat.le_div_iff_mul_le hpPrime.pos).1 hOneLe
      simpa only [one_mul] using hpLe
  · right
    refine ⟨r, Nat.one_le_iff_ne_zero.mpr hrZero, rfl, ?_⟩
    rw [mem_stationaryPrimeLayer]
    refine ⟨hpPrime, hnUpper, ?_⟩
    have hrowLe : 2 * r + 1 ≤ (2 * n) / p := by omega
    have hmul := (Nat.le_div_iff_mul_le hpPrime.pos).1 hrowLe
    simpa only [Nat.mul_comm] using hmul

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

theorem largeCentralCofactorProduct_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    0 < largeCentralCofactorProduct n X q := by
  exact Finset.prod_pos fun p hp ↦ largeCentralCofactor_pos hq hp

theorem centralAnchorDivisor_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    0 < centralAnchorDivisor n X q := by
  exact mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
    (largeCentralCofactorProduct_pos hq)







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TailValuationTwoSided -/
section


/-!
# Two-sided fixed-prime tail valuation bounds

The factorial quotient over `(a,a+h]` has `p`-valuation
`h/(p-1) + O(log(a+h))`.  This file records an exact integer version of
both sides.  The lower bound comes from Legendre's digit-sum identity and
is strong enough for the strict reserve in the central-anchor construction.
-/

namespace Erdos390.WholePaper

noncomputable section

private theorem digits_sum_le_pred_mul_length
    {p n : ℕ} (hp : p.Prime) :
    (p.digits n).sum ≤ (p - 1) * (p.digits n).length := by
  have listBound : ∀ l : List ℕ,
      (∀ d ∈ l, d < p) → l.sum ≤ (p - 1) * l.length := by
    intro l hd
    induction l with
    | nil => simp
    | cons d l ih =>
        have hdHead : d ≤ p - 1 := by
          have := hd d (by simp)
          omega
        have hdTail : ∀ e ∈ l, e < p := by
          intro e he
          exact hd e (by simp [he])
        have ih' := ih hdTail
        simp only [List.sum_cons, List.length_cons]
        calc
          d + l.sum ≤ (p - 1) + (p - 1) * l.length :=
            Nat.add_le_add hdHead ih'
          _ = (p - 1) * (l.length + 1) := by
            rw [Nat.mul_succ]
            omega
  exact listBound (p.digits n) (fun d hd ↦
    Nat.digits_lt_base hp.one_lt hd)

theorem digits_sum_le_pred_mul_log2_add_one
    {p n : ℕ} (hp : p.Prime) :
    (p.digits n).sum ≤ (p - 1) * (Nat.log2 n + 1) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hlength := digits_sum_le_pred_mul_length (n := n) hp
  rw [Nat.digits_len p n hp.one_lt hn] at hlength
  have hlog : Nat.log p n ≤ Nat.log 2 n :=
    Nat.log_anti_left Nat.one_lt_two hp.two_le
  rw [← Nat.log2_eq_log_two] at hlog
  exact hlength.trans (Nat.mul_le_mul_left (p - 1)
    (Nat.add_le_add_right hlog 1))

/-- Exact lower Legendre bound, written without integer division. -/
theorem factorialValuation_lower_cross
    {h p : ℕ} (hp : p.Prime) :
    h ≤ (p - 1) *
      (h.factorial.factorization p + Nat.log2 h + 1) := by
  have hdigitsLe : (p.digits h).sum ≤ h := Nat.digit_sum_le p h
  have hlegendre := Nat.sub_one_mul_factorization_factorial
    (n := h) hp
  have hrecover :
      (p - 1) * h.factorial.factorization p + (p.digits h).sum = h := by
    omega
  have hdigitsBound := digits_sum_le_pred_mul_log2_add_one
    (n := h) hp
  calc
    h = (p - 1) * h.factorial.factorization p +
        (p.digits h).sum := hrecover.symm
    _ ≤ (p - 1) * h.factorial.factorization p +
        (p - 1) * (Nat.log2 h + 1) :=
      Nat.add_le_add_left hdigitsBound _
    _ = (p - 1) *
        (h.factorial.factorization p + Nat.log2 h + 1) := by ring

/-- The interval `(a,a+h]` contains at least the valuation of `h!`, hence
inherits the exact lower Legendre bound. -/
theorem factorialValuationSub_lower_cross
    {a h p : ℕ} (hp : p.Prime) :
    h ≤ (p - 1) *
      ((a + h).factorial.factorization p - a.factorial.factorization p +
        Nat.log2 h + 1) := by
  have htail : h.factorial.factorization p ≤
      (a + h).factorial.factorization p - a.factorial.factorization p := by
    rw [factorialValuationSub_eq_choose_add_factorialValuation]
    omega
  exact (factorialValuation_lower_cross hp).trans
    (Nat.mul_le_mul_left (p - 1) (by omega))



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

/-- Every upper endpoint lies weakly above `2n`. -/
theorem two_mul_le_upperEndpoint (n h : ℕ) :
    2 * n ≤ upperEndpoint n h := by
  simp only [upperEndpoint, Nat.le_add_right]

/-- A tail of length at most `n` gives an endpoint at most `3n`. -/
theorem upperEndpoint_le_three_mul {n h : ℕ} (hh : h ≤ n) :
    upperEndpoint n h ≤ 3 * n := by
  simp only [upperEndpoint]
  omega



/-- The paper's scaled upper endpoint is eventually in `[2n,3n]`. -/
theorem eventually_upperScaledEndpoint_bounds {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      2 * n ≤ upperEndpoint n (upperTailLength c n) ∧
        upperEndpoint n (upperTailLength c n) ≤ 3 * n := by
  filter_upwards [eventually_upperTailLength_le hc] with n hn
  exact ⟨two_mul_le_upperEndpoint n (upperTailLength c n),
    upperEndpoint_le_three_mul hn⟩











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.UpperProductAssembly -/
section


/-!
# Exact upper-bound product assembly

This is the division-free algebra at the end of the paper.  A central anchor
set removes the central binomial coefficient together with a divisor `D` of
the tail.  A disjoint residual tail set removes the complementary tail
product.  Their union is therefore an exact complement representation, and
the complement lemma recovers a factorization of `n!`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem centralTailProduct_mul_centralFactorial (n h : ℕ) :
    centralTailProduct n h * (2 * n).factorial =
      (2 * n + h).factorial := by
  exact factorInterval_prod_mul_factorial (by omega)













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorTailDivisibility -/
section


/-!
# From central-anchor valuation reserve to literal tail divisibility

The analytic part of the central-anchor argument produces inequalities at a
fixed finite set of primes.  This file supplies the exact arithmetic bridge:
the factorial-tail valuation is the valuation of the literal tail product,
and bounds on the finite support of the anchor divisor imply actual natural-
number divisibility.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The literal tail product is positive, including when the tail is empty. -/
theorem centralTailProduct_pos (n h : ℕ) : 0 < centralTailProduct n h := by
  exact Finset.prod_pos fun a ha ↦ by
    have haMem : a ∈ Finset.Ioc (2 * n) (2 * n + h) := ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp haMem).1

/-- Exact valuation of the literal product over `(2n,2n+h]`. -/
theorem centralTailProduct_factorization (n h p : ℕ) :
    (centralTailProduct n h).factorization p =
      (2 * n + h).factorial.factorization p -
        (2 * n).factorial.factorization p := by
  have hproduct := congrArg (fun m : ℕ ↦ m.factorization p)
    (centralTailProduct_mul_centralFactorial n h)
  have htailNe : centralTailProduct n h ≠ 0 :=
    (centralTailProduct_pos n h).ne'
  have hfactorialNe : (2 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  change
    (centralTailProduct n h * (2 * n).factorial).factorization p =
      (2 * n + h).factorial.factorization p at hproduct
  rw [Nat.factorization_mul htailNe hfactorialNe] at hproduct
  simp only [Finsupp.add_apply] at hproduct
  omega

/-- The asymptotic module's tail valuation is literally the valuation of the
corresponding finite product. -/
theorem upperTailValuation_eq_centralTailProduct_factorization
    (c : ℝ) (n p : ℕ) :
    upperTailValuation c n p =
      (centralTailProduct n (upperTailLength c n)).factorization p := by
  rw [centralTailProduct_factorization]
  rfl











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























/-- Chosen pairs are injective because their marker coordinates are distinct. -/
theorem bankChosenMarkerDonor_injective
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    Function.Injective (bankChosenMarkerDonor eligible) := by
  intro marker marker' hpairs
  apply Subtype.ext
  exact congrArg Prod.fst hpairs





theorem card_bankMarkerDonorPairs
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    (bankMarkerDonorPairs eligible).card =
      bankEligibleMarkerCount eligible := by
  unfold bankMarkerDonorPairs bankEligibleMarkerCount
  rw [Finset.card_image_of_injective _
    (bankChosenMarkerDonor_injective eligible)]
  simp













theorem card_bankOrientationPoolFirst
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    (bankOrientationPoolFirst eligible).card =
      (bankMarkerDonorPairs eligible).card / 2 := by
  exact (Classical.choose_spec
    (half_card_subset_exists (bankMarkerDonorPairs eligible))).2





theorem card_bankOrientationPoolSecond
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    (bankOrientationPoolSecond eligible).card =
      (bankMarkerDonorPairs eligible).card -
        (bankMarkerDonorPairs eligible).card / 2 := by
  unfold bankOrientationPoolSecond
  rw [Finset.card_sdiff_of_subset
    (bankOrientationPoolFirst_subset_pairs eligible),
    card_bankOrientationPoolFirst]

/-- The two orientation-pool cardinalities differ by at most one.  The first
pool is the smaller one when the total cardinality is odd. -/
theorem bankOrientationPools_card_balanced
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    (bankOrientationPoolFirst eligible).card ≤
        (bankOrientationPoolSecond eligible).card ∧
      (bankOrientationPoolSecond eligible).card ≤
        (bankOrientationPoolFirst eligible).card + 1 := by
  rw [card_bankOrientationPoolFirst, card_bankOrientationPoolSecond]
  omega







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomPoolMatching -/
section


/-!
# Finite matching for the eight oriented bottom pools

The four bottom moves and their two orientations give eight literal pool
labels.  This file assumes only actual finite request and occurrence pools,
pointwise cardinality bounds, and pairwise disjointness of the occurrence
pools.  It then chooses an injective occurrence assignment.  No analytic
estimate asserting that the capacity hypotheses hold appears here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section















/-- Pointwise capacity is sufficient to choose a matching in every pool. -/
theorem bankBottomPoolMatching_nonempty
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (available : BankBottomOrientationPool → Finset Occurrence)
    (hcapacity : ∀ pool,
      bankBottomPoolDemand requests poolOf pool ≤
        bankBottomPoolCapacity available pool) :
    Nonempty (BankBottomPoolMatching requests poolOf available) := by
  let embedding : (pool : BankBottomOrientationPool) →
      ↑(bankBottomRequestsInPool requests poolOf pool) ↪
        ↑(available pool) := fun pool ↦
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_coe, bankBottomPoolDemand,
        bankBottomPoolCapacity] using hcapacity pool))
  exact ⟨⟨embedding⟩⟩







theorem bankBottomLabelRequest_injective
    {Request : Type*} [DecidableEq Request]
    {requests : Finset Request}
    (poolOf : Request → BankBottomOrientationPool) :
    Function.Injective
      (bankBottomLabelRequest (requests := requests) poolOf) := by
  intro request request' heq
  apply Subtype.ext
  exact congrArg
    (fun labeled : BankBottomLabeledRequest requests poolOf ↦ labeled.2.1) heq





/-- Disjoint actual pools make the sigma-level assignment globally injective. -/
theorem BankBottomPoolMatching.slotOfLabeledRequest_injective
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (hpools : ∀ {pool pool' : BankBottomOrientationPool},
      pool ≠ pool' → Disjoint (available pool) (available pool')) :
    Function.Injective matching.slotOfLabeledRequest := by
  rintro ⟨pool, request⟩ ⟨pool', request'⟩ heq
  by_cases hp : pool = pool'
  · subst pool'
    have hembedding : matching.toEmbedding pool request =
        matching.toEmbedding pool request' := by
      apply Subtype.ext
      exact heq
    have hrequest := (matching.toEmbedding pool).injective hembedding
    subst request'
    rfl
  · have hleft : matching.slotOfLabeledRequest ⟨pool, request⟩ ∈
        available pool :=
      matching.slotOfLabeledRequest_mem ⟨pool, request⟩
    have hright : matching.slotOfLabeledRequest ⟨pool, request⟩ ∈
        available pool' := by
      rw [heq]
      exact matching.slotOfLabeledRequest_mem ⟨pool', request'⟩
    exact False.elim ((Finset.disjoint_left.mp (hpools hp)) hleft hright)





theorem BankBottomPoolMatching.matchedSlot_injective
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (hpools : ∀ {pool pool' : BankBottomOrientationPool},
      pool ≠ pool' → Disjoint (available pool) (available pool')) :
    Function.Injective matching.matchedSlot :=
  (matching.slotOfLabeledRequest_injective hpools).comp
    (bankBottomLabelRequest_injective (requests := requests) poolOf)









/-- Concrete finite greedy/matching conclusion for all eight pools at once. -/
theorem exists_bankBottomPool_injective_assignment
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (available : BankBottomOrientationPool → Finset Occurrence)
    (hcapacity : ∀ pool,
      bankBottomPoolDemand requests poolOf pool ≤
        bankBottomPoolCapacity available pool)
    (hpools : ∀ {pool pool' : BankBottomOrientationPool},
      pool ≠ pool' → Disjoint (available pool) (available pool')) :
    ∃ matching : BankBottomPoolMatching requests poolOf available,
      Function.Injective matching.matchedSlot ∧
        ∀ request : ↑requests,
          matching.matchedSlot request ∈ available (poolOf request.1) := by
  let matching := Classical.choice
    (bankBottomPoolMatching_nonempty requests poolOf available hcapacity)
  exact ⟨matching, matching.matchedSlot_injective hpools,
    matching.matchedSlot_mem⟩

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



































/-- The two oriented subintervals are disjoint. -/
theorem bankBottomOrientationIntervals_disjoint
    (n M : ℕ) (move : BankBottomMove) :
    Disjoint
      (bankBottomOrientedMarkerInterval n M (move, .downward))
      (bankBottomOrientedMarkerInterval n M (move, .upward)) := by
  simp only [bankBottomOrientedMarkerInterval]
  exact Finset.Ioc_disjoint_Ioc_of_le le_rfl







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









/-- Under the eventual narrow-endpoint inequality, the four marker rows are
pairwise disjoint. -/
theorem bankBottomMarkerIntervals_disjoint
    {n M : ℕ} (hM : 5 * M ≤ 12 * n)
    {move move' : BankBottomMove} (hmove : move ≠ move') :
    Disjoint (bankBottomMarkerInterval n M move)
      (bankBottomMarkerInterval n M move') := by
  rw [Finset.disjoint_left]
  intro marker hmarker hmarker'
  cases move <;> cases move' <;>
    simp_all [bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc] <;> omega

/-- Hence any oriented subpools belonging to distinct rows are disjoint. -/
theorem bankBottomOrientedMarkerIntervals_disjoint_of_move_ne
    {n M : ℕ} (hTwoN : 2 * n ≤ M) (hM : 5 * M ≤ 12 * n)
    {pool pool' : BankBottomOrientationPool}
    (hmove : pool.1 ≠ pool'.1) :
    Disjoint (bankBottomOrientedMarkerInterval n M pool)
      (bankBottomOrientedMarkerInterval n M pool') := by
  rw [Finset.disjoint_left]
  intro marker hmarker hmarker'
  exact (Finset.disjoint_left.mp
      (bankBottomMarkerIntervals_disjoint hM hmove))
    (bankBottomOrientedMarkerInterval_subset hTwoN pool hmarker)
    (bankBottomOrientedMarkerInterval_subset hTwoN pool' hmarker')

/-- All eight oriented bottom marker intervals are pairwise disjoint. -/
theorem bankBottomOrientedMarkerIntervals_disjoint
    {n M : ℕ} (hTwoN : 2 * n ≤ M) (hM : 5 * M ≤ 12 * n)
    {pool pool' : BankBottomOrientationPool} (hpools : pool ≠ pool') :
    Disjoint (bankBottomOrientedMarkerInterval n M pool)
      (bankBottomOrientedMarkerInterval n M pool') := by
  by_cases hmove : pool.1 = pool'.1
  · rcases pool with ⟨move, orientation⟩
    rcases pool' with ⟨move', orientation'⟩
    simp only at hmove
    subst move'
    cases orientation <;> cases orientation'
    · simp at hpools
    · exact bankBottomOrientationIntervals_disjoint n M move
    · exact (bankBottomOrientationIntervals_disjoint n M move).symm
    · simp at hpools
  · exact bankBottomOrientedMarkerIntervals_disjoint_of_move_ne
      hTwoN hM hmove

theorem bankBottomOrientedMarkerPrimes_disjoint
    {n M : ℕ} (hTwoN : 2 * n ≤ M) (hM : 5 * M ≤ 12 * n)
    {pool pool' : BankBottomOrientationPool} (hpools : pool ≠ pool') :
    Disjoint (bankBottomOrientedMarkerPrimes n M pool)
      (bankBottomOrientedMarkerPrimes n M pool') := by
  rw [Finset.disjoint_left]
  intro marker hmarker hmarker'
  exact (Finset.disjoint_left.mp
      (bankBottomOrientedMarkerIntervals_disjoint hTwoN hM hpools))
    (Finset.mem_filter.mp hmarker).1
    (Finset.mem_filter.mp hmarker').1



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.SafeShortIntervalPrimeCounting -/
section


/-!
# Safe prime counting in moving short intervals

This module extracts the short-interval consequence that is actually needed
for the bottom marker banks.  The proof does **not** subtract two copies of
the public `O(x / log(x)^2)` remainder for `pi`.  Such a subtraction would
leave an error on the same scale as the desired answer.

Instead, it subtracts the stronger audited estimates
`theta(x) - x = O(x / log(x)^2)`.  At asymptotically linear endpoints this
error is `o(n / log n)`.  The logarithmic weights on a prime interval are
then squeezed between the logarithms of its two endpoints.  Dividing those
weights out supplies the additional logarithm and gives an unweighted prime
count on the scale `n / (log n)^2`.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

noncomputable section



private theorem movingEndpoint_cast_tendsto_atTop
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto (fun n : ℕ ↦ (m n : ℝ)) atTop atTop := by
  have hratio :
      ∀ᶠ n : ℕ in atTop, a / 2 ≤ (m n : ℝ) / (n : ℝ) :=
    hm.eventually (eventually_ge_nhds (half_lt_self ha))
  have hbase :
      Tendsto (fun n : ℕ ↦ (a / 2) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos ha)
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards [hratio, eventually_gt_atTop 0] with n hnRatio hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (le_div_iff₀ hnR).mp hnRatio

/-- Logs at any asymptotically positive linear endpoint can be replaced by
`log n` in a multiplicative limit.  This is one side of the later explicit
logarithmic squeeze. -/
theorem movingEndpoint_log_ratio_tendsto_one
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / Real.log (m n : ℝ))
      atTop (nhds 1) := by
  let u : ℕ → ℝ := fun n ↦ (m n : ℝ) / (n : ℝ)
  have hu : Tendsto u atTop (nhds a) := hm
  have hlogu : Tendsto (fun n ↦ Real.log (u n)) atTop
      (nhds (Real.log a)) :=
    (Real.continuousAt_log ha.ne').tendsto.comp hu
  have hlogn : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto
      (fun n : ℕ ↦ Real.log (u n) / Real.log (n : ℝ))
      atTop (nhds 0) := by
    simpa using hlogu.div_atTop hlogn
  have hden : Tendsto
      (fun n : ℕ ↦ 1 + Real.log (u n) / Real.log (n : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsmall
  have hinv : Tendsto
      (fun n : ℕ ↦ 1 / (1 + Real.log (u n) / Real.log (n : ℝ)))
      atTop (nhds 1) := by
    have hnum : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    convert hnum.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
    norm_num
  apply hinv.congr'
  have huPos : ∀ᶠ n : ℕ in atTop, 0 < u n :=
    hu.eventually (eventually_gt_nhds ha)
  have hmTop := movingEndpoint_cast_tendsto_atTop ha hm
  filter_upwards [huPos, eventually_gt_atTop 1,
      hmTop.eventually (eventually_gt_atTop 1)] with n hun hn hmn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlogn : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogm : Real.log (m n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hmn)).ne'
  have humul : u n * (n : ℝ) = (m n : ℝ) := by
    dsimp [u]
    field_simp
  rw [← humul, Real.log_mul hun.ne' hnPos.ne']
  field_simp
  ring

private theorem movingEndpoint_div_log_sq_isLittleO_secondOrderScale
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    (fun n : ℕ ↦ (m n : ℝ) / Real.log (m n : ℝ) ^ 2) =o[atTop]
      Erdos390.WholePaper.secondOrderScale := by
  have hmTop := movingEndpoint_cast_tendsto_atTop ha hm
  have hlogRatio := movingEndpoint_log_ratio_tendsto_one ha hm
  have hinvLog : Tendsto
      (fun n : ℕ ↦ 1 / Real.log (m n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div] using
      (Real.tendsto_log_atTop.comp hmTop).inv_tendsto_atTop
  have hratio0 : Tendsto
      (fun n : ℕ ↦
        ((m n : ℝ) / (n : ℝ)) *
          (Real.log (n : ℝ) / Real.log (m n : ℝ)) *
          (1 / Real.log (m n : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_one, mul_zero] using (hm.mul hlogRatio).mul hinvLog
  have hratio : Tendsto
      (fun n : ℕ ↦
        ((m n : ℝ) / Real.log (m n : ℝ) ^ 2) /
          Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds 0) := by
    apply hratio0.congr'
    filter_upwards [eventually_gt_atTop 1,
        hmTop.eventually (eventually_gt_atTop 1)] with n hn hmn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
    have hlogn : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hlogm : Real.log (m n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hmn)).ne'
    rw [Erdos390.WholePaper.secondOrderScale]
    field_simp
  apply (isLittleO_iff_tendsto' ?_).mpr hratio
  filter_upwards [Erdos390.WholePaper.eventually_secondOrderScale_pos] with
      n hscale hzero
  exact (hscale.ne' hzero).elim

/-- The audited quantitative estimate for `theta` is negligible on the
`n / log n` length scale at every asymptotically positive linear endpoint. -/
theorem theta_movingEndpoint_error_normalized_tendsto_zero
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦
        (Chebyshev.theta (m n : ℝ) - (m n : ℝ)) /
          Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds 0) := by
  have hmTop := movingEndpoint_cast_tendsto_atTop ha hm
  have htheta0 :=
    (Erdos390.Full.FriableAsymptotic.theta_error_isBigO_log_power 2).comp_tendsto
      hmTop
  have htheta :
      (fun n : ℕ ↦ Chebyshev.theta (m n : ℝ) - (m n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (m n : ℝ) / Real.log (m n : ℝ) ^ 2) := by
    simpa only [Function.comp_def, Pi.sub_apply, id_eq,
      Real.rpow_two] using htheta0
  exact (htheta.trans_isLittleO
    (movingEndpoint_div_log_sq_isLittleO_secondOrderScale ha hm)).tendsto_div_nhds_zero

/-- Subtracting the two endpoint estimates gives the correctly normalized
`theta`-mass of a moving short interval. -/
theorem theta_shortMovingInterval_normalized_tendsto
    {lower upper : ℕ → ℕ} {a delta : ℝ} (ha : 0 < a)
    (hlower : Tendsto
      (fun n : ℕ ↦ (lower n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hupper : Tendsto
      (fun n : ℕ ↦ (upper n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hgap : Tendsto
      (fun n : ℕ ↦ ((upper n : ℝ) - (lower n : ℝ)) /
        Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds delta)) :
    Tendsto
      (fun n : ℕ ↦
        (Chebyshev.theta (upper n : ℝ) -
            Chebyshev.theta (lower n : ℝ)) /
          Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds delta) := by
  have hupperError :=
    theta_movingEndpoint_error_normalized_tendsto_zero ha hupper
  have hlowerError :=
    theta_movingEndpoint_error_normalized_tendsto_zero ha hlower
  have htotal := (hupperError.sub hlowerError).add hgap
  have htotal' : Tendsto
      (fun n : ℕ ↦
        (Chebyshev.theta (upper n : ℝ) - (upper n : ℝ)) /
            Erdos390.WholePaper.secondOrderScale n -
          (Chebyshev.theta (lower n : ℝ) - (lower n : ℝ)) /
            Erdos390.WholePaper.secondOrderScale n +
          ((upper n : ℝ) - (lower n : ℝ)) /
            Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds delta) := by
    simpa using htotal
  apply htotal'.congr'
  filter_upwards [Erdos390.WholePaper.eventually_secondOrderScale_pos] with
      n hscale
  have hscale0 : Erdos390.WholePaper.secondOrderScale n ≠ 0 := hscale.ne'
  field_simp
  ring

/-- Exact identification of the `theta` difference with the logarithmically
weighted primes in a natural half-open interval. -/
theorem theta_natCast_sub_eq_sum_prime_Ioc
    {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) =
      ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log (p : ℝ) := by
  classical
  let small : Finset ℕ := (Finset.Icc 0 a).filter Nat.Prime
  let large : Finset ℕ := (Finset.Icc 0 b).filter Nat.Prime
  have hsubset : small ⊆ large := by
    intro p hp
    simp only [small, large, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hab⟩, hp.2⟩
  have hdiff : large \ small = (Finset.Ioc a b).filter Nat.Prime := by
    ext p
    simp only [small, large, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨_hp0, hpb⟩, hpPrime⟩, hpNotSmall⟩
      have hap : a < p := by
        by_contra hpa
        exact hpNotSmall ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hpa⟩, hpPrime⟩
      exact ⟨⟨hap, hpb⟩, hpPrime⟩
    · rintro ⟨⟨hap, hpb⟩, hpPrime⟩
      exact ⟨⟨⟨Nat.zero_le p, hpb⟩, hpPrime⟩, by
        intro hpSmall
        exact (not_le_of_gt hap) hpSmall.1.2⟩
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  change (∑ p ∈ large, Real.log (p : ℝ)) -
      ∑ p ∈ small, Real.log (p : ℝ) = _
  rw [← Finset.sum_sdiff hsubset]
  rw [hdiff]
  ring

/-- On a positive natural interval, the endpoint logarithms give the exact
upper and lower weights needed to squeeze its prime cardinality. -/
theorem prime_Ioc_log_weight_bounds
    {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) * Real.log (a : ℝ) ≤
        Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) ∧
      Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) ≤
        (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) * Real.log (b : ℝ) := by
  classical
  let primes := (Finset.Ioc a b).filter Nat.Prime
  have hlower :
      primes.card • Real.log (a : ℝ) ≤
        ∑ p ∈ primes, Real.log (p : ℝ) := by
    apply Finset.card_nsmul_le_sum
    intro p hp
    have hpIoc : a < p ∧ p ≤ b :=
      Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    apply Real.log_le_log (by exact_mod_cast ha)
    exact_mod_cast hpIoc.1.le
  have hupper :
      (∑ p ∈ primes, Real.log (p : ℝ)) ≤
        primes.card • Real.log (b : ℝ) := by
    apply Finset.sum_le_card_nsmul
    intro p hp
    have hpIoc : a < p ∧ p ≤ b :=
      Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hpPos : 0 < p := ha.trans hpIoc.1
    apply Real.log_le_log (by exact_mod_cast hpPos)
    exact_mod_cast hpIoc.2
  have hexact := theta_natCast_sub_eq_sum_prime_Ioc hab
  constructor
  · simpa only [primes, nsmul_eq_mul, hexact] using hlower
  · simpa only [primes, nsmul_eq_mul, hexact] using hupper



/-- Safe short-interval PNT at arbitrary moving endpoints.  The hypotheses
make the common linear location and the smaller `n / log n` endpoint gap
fully explicit; the conclusion counts actual primes in `(lower, upper]` on
the finer `n / (log n)^2` scale. -/
theorem prime_Ioc_shortMovingInterval_normalized_tendsto
    {lower upper : ℕ → ℕ} {a delta : ℝ} (ha : 0 < a)
    (hlower : Tendsto
      (fun n : ℕ ↦ (lower n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hupper : Tendsto
      (fun n : ℕ ↦ (upper n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hgap : Tendsto
      (fun n : ℕ ↦ ((upper n : ℝ) - (lower n : ℝ)) /
        Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds delta))
    (horder : ∀ᶠ n : ℕ in atTop, lower n ≤ upper n) :
    Tendsto
      (fun n : ℕ ↦
        (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
          shortIntervalPrimeScale n)
      atTop (nhds delta) := by
  have htheta := theta_shortMovingInterval_normalized_tendsto
    ha hlower hupper hgap
  have hlogLower := movingEndpoint_log_ratio_tendsto_one ha hlower
  have hlogUpper := movingEndpoint_log_ratio_tendsto_one ha hupper
  have hlowerLimit := htheta.mul hlogUpper
  have hupperLimit := htheta.mul hlogLower
  have hlowerTop := movingEndpoint_cast_tendsto_atTop ha hlower
  have hupperTop := movingEndpoint_cast_tendsto_atTop ha hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [mul_one] using hlowerLimit)
    (by simpa only [mul_one] using hupperLimit)
  · filter_upwards [horder,
      Erdos390.WholePaper.eventually_secondOrderScale_pos,
      eventually_gt_atTop 1,
      hlowerTop.eventually (eventually_gt_atTop 1),
      hupperTop.eventually (eventually_gt_atTop 1)] with
      n hle hscale hn hlowerOne hupperOne
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hn)
    have hlogUpperPos : 0 < Real.log (upper n : ℝ) :=
      Real.log_pos (by exact_mod_cast hupperOne)
    have hbounds := prime_Ioc_log_weight_bounds
      (show 0 < lower n by exact_mod_cast (lt_trans zero_lt_one hlowerOne)) hle
    have hdenPos : 0 < Erdos390.WholePaper.secondOrderScale n /
        Real.log (n : ℝ) := div_pos hscale hlogn
    calc
      ((Chebyshev.theta (upper n : ℝ) -
            Chebyshev.theta (lower n : ℝ)) /
          Erdos390.WholePaper.secondOrderScale n) *
          (Real.log (n : ℝ) / Real.log (upper n : ℝ)) =
        ((Chebyshev.theta (upper n : ℝ) -
            Chebyshev.theta (lower n : ℝ)) /
          Real.log (upper n : ℝ)) /
            (Erdos390.WholePaper.secondOrderScale n /
              Real.log (n : ℝ)) := by field_simp
      _ ≤ (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
            (Erdos390.WholePaper.secondOrderScale n /
              Real.log (n : ℝ)) := by
        apply div_le_div_of_nonneg_right _ hdenPos.le
        exact (div_le_iff₀ hlogUpperPos).2 hbounds.2
      _ = (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
            shortIntervalPrimeScale n := rfl
  · filter_upwards [horder,
      Erdos390.WholePaper.eventually_secondOrderScale_pos,
      eventually_gt_atTop 1,
      hlowerTop.eventually (eventually_gt_atTop 1),
      hupperTop.eventually (eventually_gt_atTop 1)] with
      n hle hscale hn hlowerOne _hupperOne
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hn)
    have hlogLowerPos : 0 < Real.log (lower n : ℝ) :=
      Real.log_pos (by exact_mod_cast hlowerOne)
    have hbounds := prime_Ioc_log_weight_bounds
      (show 0 < lower n by exact_mod_cast (lt_trans zero_lt_one hlowerOne)) hle
    have hdenPos : 0 < Erdos390.WholePaper.secondOrderScale n /
        Real.log (n : ℝ) := div_pos hscale hlogn
    calc
      (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
          shortIntervalPrimeScale n =
        (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
          (Erdos390.WholePaper.secondOrderScale n /
            Real.log (n : ℝ)) := rfl
      _ ≤ ((Chebyshev.theta (upper n : ℝ) -
            Chebyshev.theta (lower n : ℝ)) /
          Real.log (lower n : ℝ)) /
            (Erdos390.WholePaper.secondOrderScale n /
              Real.log (n : ℝ)) := by
        apply div_le_div_of_nonneg_right _ hdenPos.le
        exact (le_div_iff₀ hlogLowerPos).2 hbounds.1
      _ = ((Chebyshev.theta (upper n : ℝ) -
            Chebyshev.theta (lower n : ℝ)) /
          Erdos390.WholePaper.secondOrderScale n) *
            (Real.log (n : ℝ) / Real.log (lower n : ℝ)) := by field_simp



end

end Erdos390.WholePaper.SafePrimeCounting

end

/- Source module: Erdos390.WholePaper.BankBottomMarkerPoolScale -/
section


/-!
# Prime-counting scales for bottom marker pools

The bottom intervals have length of order `n / log n`, while their prime
cardinality has order `n / log n ^ 2`.  Consequently their cardinality
divided by `secondOrderScale n = n / log n` tends to zero, not to a positive
constant.  This file records that coarse-scale fact and then applies the
audited `theta`-difference squeeze to obtain the positive constants on the
finer scale `secondOrderScale n / log n`.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section



private theorem natDiv_endpoint_ratio_tendsto
    {m : ℕ → ℕ} {a : ℝ}
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a))
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun n : ℕ ↦ ((m n / d : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a / (d : ℝ))) := by
  have hmain :
      Tendsto
        (fun n : ℕ ↦ ((m n : ℝ) / (n : ℝ)) / (d : ℝ))
        atTop (nhds (a / (d : ℝ))) :=
    hm.div_const (d : ℝ)
  have hinv :
      Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hlower :
      Tendsto
        (fun n : ℕ ↦
          ((m n : ℝ) / (n : ℝ)) / (d : ℝ) - 1 / (n : ℝ))
        atTop (nhds (a / (d : ℝ))) := by
    simpa only [sub_zero] using hmain.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hmain
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hfloor :
        (m n : ℝ) / (d : ℝ) < ((m n / d : ℕ) : ℝ) + 1 := by
      simpa only [Nat.floor_div_eq_div] using
        (Nat.lt_floor_add_one ((m n : ℝ) / (d : ℝ)))
    have hbase :
        (m n : ℝ) / (d : ℝ) - 1 ≤ ((m n / d : ℕ) : ℝ) := by
      linarith
    calc
      ((m n : ℝ) / (n : ℝ)) / (d : ℝ) - 1 / (n : ℝ) =
          ((m n : ℝ) / (d : ℝ) - 1) / (n : ℝ) := by
            field_simp
      _ ≤ ((m n / d : ℕ) : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hbase hnR.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hcast :
        ((m n / d : ℕ) : ℝ) ≤ (m n : ℝ) / (d : ℝ) :=
      Nat.cast_div_le
    calc
      ((m n / d : ℕ) : ℝ) / (n : ℝ) ≤
          ((m n : ℝ) / (d : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hcast hnR.le
      _ = ((m n : ℝ) / (n : ℝ)) / (d : ℝ) := by
        field_simp

private theorem natCast_self_ratio_tendsto_one :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / (n : ℝ)) atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (div_self (by exact_mod_cast hn.ne')).symm

private theorem two_mul_natCast_ratio_tendsto_two :
    Tendsto (fun n : ℕ ↦ ((2 * n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

private theorem upperScaledEndpoint_ratio_tendsto_two
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (upperEndpoint n (upperTailLength c n) : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
  have hsum : Tendsto
      (fun n : ℕ ↦ (2 : ℝ) +
        (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
    simpa only [add_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _n : ℕ ↦ (2 : ℝ)) atTop (nhds 2)).add
          (upperTailLength_ratio_tendsto_zero hc)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp



theorem bankBottomMarkerBase_pos (move : BankBottomMove) :
    0 < bankBottomMarkerBase move := by
  cases move <;> norm_num [bankBottomMarkerBase]

theorem bankBottomMarkerLower_ratio_tendsto (move : BankBottomMove) :
    Tendsto
      (fun n : ℕ ↦ (bankBottomMarkerLower n move : ℝ) / (n : ℝ))
      atTop (nhds (bankBottomMarkerBase move)) := by
  cases move
  · simpa only [bankBottomMarkerLower, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto natCast_self_ratio_tendsto_one 3 (by omega)
  · simpa only [bankBottomMarkerLower, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto two_mul_natCast_ratio_tendsto_two 5 (by omega)
  · simpa only [bankBottomMarkerLower, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto two_mul_natCast_ratio_tendsto_two 3 (by omega)
  · simpa only [bankBottomMarkerLower, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto natCast_self_ratio_tendsto_one 2 (by omega)

theorem bankBottomMarkerUpper_ratio_tendsto
    {c : ℝ} (hc : 0 < c) (move : BankBottomMove) :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomMarkerUpper
          (upperEndpoint n (upperTailLength c n)) move : ℝ) / (n : ℝ))
      atTop (nhds (bankBottomMarkerBase move)) := by
  have hM := upperScaledEndpoint_ratio_tendsto_two hc
  cases move
  · convert natDiv_endpoint_ratio_tendsto hM 6 (by omega) using 1
    norm_num [bankBottomMarkerUpper, bankBottomMarkerBase]
  · simpa only [bankBottomMarkerUpper, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto hM 5 (by omega)
  · simpa only [bankBottomMarkerUpper, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto hM 3 (by omega)
  · convert natDiv_endpoint_ratio_tendsto hM 4 (by omega) using 1
    norm_num [bankBottomMarkerUpper, bankBottomMarkerBase]



theorem bankBottomMarkerDenominator_pos (move : BankBottomMove) :
    0 < bankBottomMarkerDenominator move := by
  cases move <;> norm_num [bankBottomMarkerDenominator]







theorem bankBottomOrientedMarkerLower_le_upper
    {n M : ℕ} (hM : 2 * n ≤ M) (pool : BankBottomOrientationPool) :
    bankBottomOrientedMarkerLower n M pool ≤
      bankBottomOrientedMarkerUpper n M pool := by
  rcases pool with ⟨move, orientation⟩
  cases orientation
  · exact bankBottomMarkerLower_le_cut n M move
  · exact bankBottomOrientationCut_le_upper hM move







/-- The integer midpoint remains at the same first-order linear location as
the two endpoints surrounding it. -/
theorem bankBottomOrientationCut_ratio_tendsto
    {c : ℝ} (hc : 0 < c) (move : BankBottomMove) :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomOrientationCut n
          (upperEndpoint n (upperTailLength c n)) move : ℝ) / (n : ℝ))
      atTop (nhds (bankBottomMarkerBase move)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (bankBottomMarkerLower_ratio_tendsto move)
    (bankBottomMarkerUpper_ratio_tendsto hc move)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ n)
    exact_mod_cast bankBottomMarkerLower_le_cut n
      (upperEndpoint n (upperTailLength c n)) move
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ n)
    exact_mod_cast bankBottomOrientationCut_le_upper
      (two_mul_le_upperEndpoint n (upperTailLength c n)) move

theorem bankBottomOrientedMarkerLower_ratio_tendsto
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomOrientedMarkerLower n
          (upperEndpoint n (upperTailLength c n)) pool : ℝ) / (n : ℝ))
      atTop (nhds (bankBottomMarkerBase pool.1)) := by
  rcases pool with ⟨move, orientation⟩
  cases orientation
  · exact bankBottomMarkerLower_ratio_tendsto move
  · exact bankBottomOrientationCut_ratio_tendsto hc move

theorem bankBottomOrientedMarkerUpper_ratio_tendsto
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomOrientedMarkerUpper n
          (upperEndpoint n (upperTailLength c n)) pool : ℝ) / (n : ℝ))
      atTop (nhds (bankBottomMarkerBase pool.1)) := by
  rcases pool with ⟨move, orientation⟩
  cases orientation
  · exact bankBottomOrientationCut_ratio_tendsto hc move
  · exact bankBottomMarkerUpper_ratio_tendsto hc move





theorem bankBottomOrientedPrimeConstant_pos
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    0 < bankBottomOrientedPrimeConstant c pool := by
  unfold bankBottomOrientedPrimeConstant
  exact div_pos hc (mul_pos (by norm_num)
    (by exact_mod_cast bankBottomMarkerDenominator_pos pool.1))



/-- Each of the eight literal oriented prime pools has the advertised
positive limiting cardinality on the finer prime scale. -/
theorem bankBottomOrientedMarkerPrimes_card_div_bankBottomPrimeScale_tendsto
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomOrientedMarkerPrimes n
          (upperEndpoint n (upperTailLength c n)) pool).card : ℝ) /
            bankBottomPrimeScale n)
      atTop (nhds (bankBottomOrientedPrimeConstant c pool)) := by
  have horder : ∀ᶠ n : ℕ in atTop,
      bankBottomOrientedMarkerLower n
          (upperEndpoint n (upperTailLength c n)) pool ≤
        bankBottomOrientedMarkerUpper n
          (upperEndpoint n (upperTailLength c n)) pool :=
    Eventually.of_forall fun n ↦ bankBottomOrientedMarkerLower_le_upper
      (two_mul_le_upperEndpoint n (upperTailLength c n)) pool
  have hshort :=
    SafePrimeCounting.prime_Ioc_shortMovingInterval_normalized_tendsto
      (bankBottomMarkerBase_pos pool.1)
      (bankBottomOrientedMarkerLower_ratio_tendsto hc pool)
      (bankBottomOrientedMarkerUpper_ratio_tendsto hc pool)
      (bankBottomOrientedMarkerGap_normalized_tendsto hc pool)
      horder
  simpa only [bankBottomOrientedMarkerPrimes,
    bankBottomOrientedMarkerInterval_eq_Ioc, bankBottomPrimeScale] using hshort









/-- The scaled endpoint is eventually narrow enough for all four rows, and
hence all eight oriented pools, to be disjoint. -/
theorem eventually_bankBottom_scaledEndpoint_narrow
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      5 * upperEndpoint n (upperTailLength c n) ≤ 12 * n := by
  have hsmall := (upperTailLength_ratio_tendsto_zero hc).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 2 / 5))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratio hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htailR :
      5 * (upperTailLength c n : ℝ) < 2 * (n : ℝ) := by
    have := (div_lt_iff₀ hnR).mp hratio
    linarith
  have htail : 5 * upperTailLength c n ≤ 2 * n := by
    exact_mod_cast htailR.le
  unfold upperEndpoint
  omega

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































/-- Every one of the eight actual request fibers has the same exact demand. -/
theorem bankBottomPaperPoolDemand_eq
    (n : ℕ) (pool : BankBottomOrientationPool) :
    bankBottomPoolDemand (bankBottomPaperRequests n)
        (bankBottomPaperRequestPool n) pool =
      bankBottomPaperDemand n := by
  rw [bankBottomPoolDemand]
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr (bankBottomPaperRequestFiberEquiv n pool),
    Fintype.card_sigma]
  change (∑ p : bankRoundingPrimeSupport n,
    Fintype.card (Fin (bankRoundingBeta n p))) = bankBottomPaperDemand n
  simp only [Fintype.card_fin, bankBottomPaperDemand]
  simpa only [Finset.univ_eq_attach] using
    (Finset.sum_attach (bankRoundingPrimeSupport n)
      (fun p ↦ bankRoundingBeta n p))





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

private theorem yNat_tendsto_atTop_BankBottomConcreteDemand : Tendsto yNat atTop atTop := by
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
      yNat_tendsto_atTop_BankBottomConcreteDemand
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
    filter_upwards [yNat_tendsto_atTop_BankBottomConcreteDemand.eventually (eventually_gt_atTop 1)]
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

private theorem yNat_isLittleO_bankBottomPrimeScale :
    (fun n : ℕ ↦ (yNat n : ℝ)) =o[atTop] bankBottomPrimeScale := by
  have hY : (fun n : ℕ ↦ (yNat n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ y n) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
    have hfloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ yNat n),
      Real.norm_eq_abs, abs_of_nonneg hyNonneg, one_mul]
    exact hfloor
  have hratio0 : Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 /
        (n : ℝ) ^ (7 / 9 : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_apply, Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2
        (by norm_num : (0 : ℝ) < 7 / 9)).tendsto_div_nhds_zero.comp
          tendsto_natCast_atTop_atTop
  have hyRatio : Tendsto
      (fun n : ℕ ↦ y n / bankBottomPrimeScale n)
      atTop (nhds 0) := by
    apply hratio0.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hnR : 0 < (n : ℝ) := by positivity
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hpow :
        (n : ℝ) ^ (2 / 9 : ℝ) * (n : ℝ) ^ (7 / 9 : ℝ) =
          (n : ℝ) := by
      rw [← Real.rpow_add hnR]
      norm_num [Real.rpow_one]
    rw [bankBottomPrimeScale, SafePrimeCounting.shortIntervalPrimeScale,
      secondOrderScale, y]
    field_simp
    nlinarith
  have hyLittle : (fun n : ℕ ↦ y n) =o[atTop]
      bankBottomPrimeScale := by
    apply (isLittleO_iff_tendsto' ?_).mpr hyRatio
    filter_upwards [eventually_gt_atTop 1] with n hn hzero
    have hscale : 0 < bankBottomPrimeScale n := by
      rw [bankBottomPrimeScale, SafePrimeCounting.shortIntervalPrimeScale]
      exact div_pos (secondOrderScale_pos (by omega))
        (Real.log_pos (by exact_mod_cast hn))
    exact (hscale.ne' hzero).elim
  exact hY.trans_isLittleO hyLittle

/-- Consequently every concrete orientation demand is negligible on the
finer bottom-prime scale. -/
theorem bankBottomPaperDemand_div_bankBottomPrimeScale_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomPaperDemand n : ℝ) / bankBottomPrimeScale n)
      atTop (nhds 0) :=
  (bankBottomPaperDemand_isBigO_yNat.trans_isLittleO
    yNat_isLittleO_bankBottomPrimeScale).tendsto_div_nhds_zero

/-- For every one of the eight pools, its concrete paper demand eventually
fits into its actual prime-marker capacity. -/
theorem eventually_bankBottomPaper_poolDemand_le_capacity
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    ∀ᶠ n : ℕ in atTop,
      bankBottomPoolDemand (bankBottomPaperRequests n)
          (bankBottomPaperRequestPool n) pool ≤
        bankBottomPoolCapacity
          (fun pool' ↦ bankBottomOrientedMarkerPrimes n
            (upperEndpoint n (upperTailLength c n)) pool') pool := by
  have hdemand := bankBottomPaperDemand_div_bankBottomPrimeScale_tendsto_zero
  have hsupply :=
    bankBottomOrientedMarkerPrimes_card_div_bankBottomPrimeScale_tendsto
      hc pool
  have hconstant := bankBottomOrientedPrimeConstant_pos hc pool
  have hdemandSmall := hdemand.eventually
    (eventually_lt_nhds (half_pos hconstant))
  have hsupplyLarge := hsupply.eventually
    (eventually_gt_nhds (half_lt_self hconstant))
  filter_upwards [hdemandSmall, hsupplyLarge,
      eventually_gt_atTop 1] with n hdemandN hsupplyN hn
  rw [bankBottomPaperPoolDemand_eq]
  unfold bankBottomPoolCapacity
  have hscale : 0 < bankBottomPrimeScale n := by
    rw [bankBottomPrimeScale, SafePrimeCounting.shortIntervalPrimeScale]
    exact div_pos (secondOrderScale_pos (by omega))
      (Real.log_pos (by exact_mod_cast hn))
  have hratio :
      (bankBottomPaperDemand n : ℝ) / bankBottomPrimeScale n <
        ((bankBottomOrientedMarkerPrimes n
          (upperEndpoint n (upperTailLength c n)) pool).card : ℝ) /
            bankBottomPrimeScale n := hdemandN.trans hsupplyN
  have hcast : (bankBottomPaperDemand n : ℝ) <
      ((bankBottomOrientedMarkerPrimes n
        (upperEndpoint n (upperTailLength c n)) pool).card : ℝ) :=
    (div_lt_div_iff_of_pos_right hscale).mp hratio
  exact_mod_cast hcast.le

/-- All eight capacity inequalities hold simultaneously. -/
theorem eventually_bankBottomPaper_all_poolDemands_le_capacity
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ pool : BankBottomOrientationPool,
      bankBottomPoolDemand (bankBottomPaperRequests n)
          (bankBottomPaperRequestPool n) pool ≤
        bankBottomPoolCapacity
          (fun pool' ↦ bankBottomOrientedMarkerPrimes n
            (upperEndpoint n (upperTailLength c n)) pool') pool := by
  rw [Filter.eventually_all]
  exact fun pool ↦ eventually_bankBottomPaper_poolDemand_le_capacity hc pool

/-- Terminal concrete allocation: eventually all signed-copy/move requests
receive globally distinct actual prime markers in their prescribed pools. -/
theorem eventually_exists_bankBottomPaper_injective_assignment
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ matching : BankBottomPoolMatching
          (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
          (fun pool ↦ bankBottomOrientedMarkerPrimes n
            (upperEndpoint n (upperTailLength c n)) pool),
        Function.Injective matching.matchedSlot ∧
          ∀ request : ↑(bankBottomPaperRequests n),
            matching.matchedSlot request ∈
              bankBottomOrientedMarkerPrimes n
                (upperEndpoint n (upperTailLength c n))
                (bankBottomPaperRequestPool n request.1) := by
  filter_upwards [eventually_bankBottomPaper_all_poolDemands_le_capacity hc,
      eventually_bankBottom_scaledEndpoint_narrow hc] with n hcapacity hnarrow
  exact exists_bankBottomPool_injective_assignment
    (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
    (fun pool ↦ bankBottomOrientedMarkerPrimes n
      (upperEndpoint n (upperTailLength c n)) pool)
    hcapacity
    (fun {_pool _pool'} hpools ↦
      bankBottomOrientedMarkerPrimes_disjoint
        (two_mul_le_upperEndpoint n (upperTailLength c n)) hnarrow hpools)

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



















/-- At the final paper endpoint `M ≤ 3n`, every bottom marker itself is at
most `n`.  Together with `n < 3P`, this is the marker guard needed by the
combined ordinary/bottom layer. -/
theorem marker_le_n (hTwoN : 2 * n ≤ M) (hMThree : M ≤ 3 * n)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.marker request ≤ n := by
  have hrow := realization.marker_mem_row hTwoN request
  cases hmove : realization.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc] at hrow <;> omega

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





























theorem componentOccurrence_mem_factorInterval
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ realization.componentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  rw [realization.componentOccurrences_eq_states_insert_donor request]
    at hoccurrence
  simp only [Finset.mem_insert, Finset.mem_singleton] at hoccurrence
  have hinterval := realization.states_donor_mem_factorInterval hTwoN request
  rcases hoccurrence with hoccurrence | hoccurrence | hoccurrence
  · simpa only [hoccurrence] using hinterval.1
  · simpa only [hoccurrence] using hinterval.2.1
  · simpa only [hoccurrence] using hinterval.2.2

theorem componentOccurrences_fiveToFour
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fiveToFour) :
    realization.componentOccurrences request =
      {4 * realization.marker request, 5 * realization.marker request,
        6 * realization.marker request} := by
  simp [componentOccurrences, hmove, bankBottomComponentOccurrences,
    bankBottomLowerState, bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

theorem componentOccurrences_fourToThree
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fourToThree) :
    realization.componentOccurrences request =
      {3 * realization.marker request, 4 * realization.marker request,
        5 * realization.marker request} := by
  simp [componentOccurrences, hmove, bankBottomComponentOccurrences,
    bankBottomLowerState, bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

theorem componentOccurrences_threeToTwo
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .threeToTwo) :
    realization.componentOccurrences request =
      {2 * realization.marker request, 3 * realization.marker request} := by
  simpa only [componentOccurrences, hmove] using
    bankBottomComponentOccurrences_threeToTwo
      (realization.marker request)

theorem componentOccurrences_twoToOne
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .twoToOne) :
    realization.componentOccurrences request =
      {2 * realization.marker request, 4 * realization.marker request} := by
  simpa only [componentOccurrences, hmove] using
    bankBottomComponentOccurrences_twoToOne
      (realization.marker request)

theorem card_componentOccurrences_fiveToFour
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fiveToFour) :
    (realization.componentOccurrences request).card = 3 := by
  rw [realization.componentOccurrences_fiveToFour request hmove]
  have hmarker : 0 < realization.marker request :=
    (realization.marker_prime request).pos
  have hfourFive : 4 * realization.marker request ≠
      5 * realization.marker request := by omega
  have hfourSix : 4 * realization.marker request ≠
      6 * realization.marker request := by omega
  have hfiveSix : 5 * realization.marker request ≠
      6 * realization.marker request := by omega
  simp [hfourFive, hfourSix, hfiveSix]

theorem card_componentOccurrences_fourToThree
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .fourToThree) :
    (realization.componentOccurrences request).card = 3 := by
  rw [realization.componentOccurrences_fourToThree request hmove]
  have hmarker : 0 < realization.marker request :=
    (realization.marker_prime request).pos
  have hthreeFour : 3 * realization.marker request ≠
      4 * realization.marker request := by omega
  have hthreeFive : 3 * realization.marker request ≠
      5 * realization.marker request := by omega
  have hfourFive : 4 * realization.marker request ≠
      5 * realization.marker request := by omega
  simp [hthreeFour, hthreeFive, hfourFive]

theorem card_componentOccurrences_threeToTwo
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .threeToTwo) :
    (realization.componentOccurrences request).card = 2 := by
  rw [realization.componentOccurrences_threeToTwo request hmove]
  have hmarker : 0 < realization.marker request :=
    (realization.marker_prime request).pos
  have htwoThree : 2 * realization.marker request ≠
      3 * realization.marker request := by omega
  simp [htwoThree]

theorem card_componentOccurrences_twoToOne
    (request : ↑(bankBottomPaperRequests n))
    (hmove : realization.move request = .twoToOne) :
    (realization.componentOccurrences request).card = 2 := by
  rw [realization.componentOccurrences_twoToOne request hmove]
  have hmarker : 0 < realization.marker request :=
    (realization.marker_prime request).pos
  have htwoFour : 2 * realization.marker request ≠
      4 * realization.marker request := by omega
  simp [htwoFour]

theorem card_componentOccurrences_le_three
    (request : ↑(bankBottomPaperRequests n)) :
    (realization.componentOccurrences request).card ≤ 3 := by
  cases hmove : realization.move request
  · rw [realization.card_componentOccurrences_fiveToFour request hmove]
  · rw [realization.card_componentOccurrences_fourToThree request hmove]
  · rw [realization.card_componentOccurrences_threeToTwo request hmove]
    omega
  · rw [realization.card_componentOccurrences_twoToOne request hmove]
    omega







end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/



namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)









/-! ## Relevant markers and marker-to-component uniqueness -/





















theorem card_relevantMarkers :
    realization.relevantMarkers.card =
      (bankBottomRelevantPaperRequests n).card := by
  rw [relevantMarkers, Finset.card_image_of_injective _
    realization.relevantMarkerMap_injective]
  simp





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

theorem BankBottomPaperRealization.card_relevantMarkers_le_demand
    {n M : ℕ} (realization : BankBottomPaperRealization n M) :
    realization.relevantMarkers.card ≤ 8 * bankBottomPaperDemand n := by
  rw [realization.card_relevantMarkers, ← card_bankBottomPaperRequests n]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem BankBottomPaperRealization.card_relevantComponentOccurrences_le_demand
    {n M : ℕ} (realization : BankBottomPaperRealization n M) :
    realization.relevantComponentOccurrences.card ≤
      24 * bankBottomPaperDemand n := by
  calc
    realization.relevantComponentOccurrences.card ≤
        (bankBottomRelevantPaperRequests n).attach.card * 3 := by
      exact Finset.card_biUnion_le_card_mul _ _ 3
        (fun request _hrequest ↦
          realization.card_componentOccurrences_le_three
            (bankBottomRelevantRequestToPaperRequest request))
    _ = 3 * (bankBottomRelevantPaperRequests n).card := by
      simp [Nat.mul_comm]
    _ ≤ 3 * (8 * bankBottomPaperDemand n) := by
      exact Nat.mul_le_mul_left 3 (by
        rw [← realization.card_relevantMarkers]
        exact realization.card_relevantMarkers_le_demand)
    _ = 24 * bankBottomPaperDemand n := by ring

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

/-- Terminal bottom-component realization.  The displayed interval and
signature conclusions concern actual matched values; the global occurrence
set and marker set used downstream are restricted to relevant requests. -/
theorem eventually_exists_bankBottomPaper_component_realization
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ realization : BankBottomPaperRealization n
          (upperEndpoint n (upperTailLength c n)),
        (∀ request : ↑(bankBottomPaperRequests n),
          realization.marker request ∈
              bankBottomOrientedMarkerPrimes n
                (upperEndpoint n (upperTailLength c n))
                (bankBottomPaperRequestPool n request.1) ∧
            realization.lowerStateFactor request ∈
              factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
            realization.upperStateFactor request ∈
              factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
            realization.donorFactor request ∈
              factorInterval n (upperEndpoint n (upperTailLength c n))) ∧
        (∀ request : ↑(bankBottomPaperRequests n),
          ∀ kind : BankBottomPaperOccurrenceKind,
            completeRoughSignature (yNat n)
                (realization.occurrenceValue request kind) =
              completeRoughSignature (yNat n)
                (realization.marker request)) ∧
        (∀ {request request' : ↑(bankBottomPaperRequests n)},
          request ≠ request' →
            Disjoint (realization.carrierValueSet request)
              (realization.carrierValueSet request') ∧
            Disjoint (realization.componentOccurrences request)
              (realization.componentOccurrences request')) ∧
        realization.relevantMarkers.card =
            (bankBottomRelevantPaperRequests n).card ∧
        realization.relevantMarkers.card ≤ 8 * bankBottomPaperDemand n ∧
        realization.relevantComponentOccurrences.card ≤
          24 * bankBottomPaperDemand n := by
  filter_upwards [eventually_exists_bankBottomPaper_injective_assignment hc,
      eventually_bankBottom_six_le_yNat,
      eventually_bankBottom_three_mul_yNat_le_self]
      with n hmatching hySix hgeometry
  rcases hmatching with ⟨matching, hinjective, _hmem⟩
  let realization : BankBottomPaperRealization n
      (upperEndpoint n (upperTailLength c n)) :=
    BankBottomPaperRealization.ofMatching matching hinjective
  have hTwoN : 2 * n ≤ upperEndpoint n (upperTailLength c n) :=
    two_mul_le_upperEndpoint n (upperTailLength c n)
  refine ⟨realization, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro request
    have hinterval := realization.states_donor_mem_factorInterval
      hTwoN request
    exact ⟨realization.marker_mem request, hinterval.1,
      hinterval.2.1, hinterval.2.2⟩
  · intro request kind
    exact realization.occurrenceValue_completeRoughSignature
      hySix request kind
  · intro request request' hrequest
    exact ⟨realization.carrierValueSets_disjoint_of_request_ne
        hTwoN hySix hgeometry hrequest,
      realization.componentOccurrences_disjoint_of_request_ne
        hTwoN hySix hgeometry hrequest⟩
  · exact realization.card_relevantMarkers
  · exact realization.card_relevantMarkers_le_demand
  · exact realization.card_relevantComponentOccurrences_le_demand

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





































/-! ## The five exceptional fixed donors -/



theorem bankOrdinarySmallDonor_pos (scale : SmallDescentScale) :
    0 < bankOrdinarySmallDonor scale := by
  cases scale <;> decide

theorem bankOrdinarySmallDonor_le_twentyThree (scale : SmallDescentScale) :
    bankOrdinarySmallDonor scale ≤ 23 := by
  cases scale <;> decide

theorem bankOrdinarySmallDonor_mem_window (scale : SmallDescentScale) :
    InOrdinaryBankDonorWindow (smallDescentScaleValue scale)
      (bankOrdinarySmallDonor scale) := by
  cases scale <;>
    norm_num [InOrdinaryBankDonorWindow, smallDescentScaleValue,
      smallDescentScaleNumerator, smallDescentScaleDenominator,
      bankOrdinarySmallDonor]

theorem bankOrdinarySmallDonor_smooth
    {n : ℕ} (hY : 23 ≤ yNat n) (scale : SmallDescentScale) :
    bankOrdinarySmallDonor scale ∈ Nat.smoothNumbers (yNat n + 1) := by
  apply Nat.mem_smoothNumbers_of_lt (bankOrdinarySmallDonor_pos scale)
  have hsmall := bankOrdinarySmallDonor_le_twentyThree scale
  omega

/-- At a small scale, primality, marker membership, and the tail-product
condition suffice: the table supplies the fixed donor-window and smoothness
conditions. -/
theorem bankOrdinarySmallPair_mem_eligible
    {n M P : ℕ} (scale : SmallDescentScale)
    (hY : 23 ≤ yNat n) (hP : P.Prime)
    (hmarker : InOrdinaryBankMarkerInterval n
      (smallDescentScaleValue scale) P)
    (htailLower : 2 * n < P * bankOrdinarySmallDonor scale)
    (htailUpper : P * bankOrdinarySmallDonor scale ≤ M) :
    (P, bankOrdinarySmallDonor scale) ∈
      bankOrdinaryEligibleRelation n M (smallDescentScaleValue scale) := by
  rw [mem_bankOrdinaryEligibleRelation]
  refine ⟨?_, hP, bankOrdinarySmallDonor_pos scale, hmarker,
    bankOrdinarySmallDonor_mem_window scale,
    bankOrdinarySmallDonor_smooth hY scale, htailLower, htailUpper⟩
  cases scale <;>
    norm_num [smallDescentScaleValue, smallDescentScaleNumerator,
      smallDescentScaleDenominator]

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





/-- The entire small-table portion of one path has an absolute, literal
bound.  In particular each of its five scale fibers has this bound. -/
theorem bankOrdinaryCoreSourcesAtSmallScale_card_le
    {q j : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q)
    (hj : j ≤ 5) :
    (bankOrdinaryCoreSourcesAtScale q j).card ≤ 17 := by
  have hsubset : bankOrdinaryCoreSourcesAtScale q j ⊆ Finset.Icc 6 22 := by
    intro s hs
    have hsData := Finset.mem_filter.mp hs
    have hspec := bankOrdinaryCoreSource_spec hq hqPower hsData.1
    have hsmall : bankOrdinaryComponentScaleIndex s ≤ 5 := by
      rw [hsData.2]
      exact hj
    exact Finset.mem_Icc.mpr ⟨hspec.1,
      bankOrdinaryComponentSource_le_twentyTwo_of_scaleIndex_le_five
        hspec.1 hsmall⟩
  calc
    (bankOrdinaryCoreSourcesAtScale q j).card ≤
        (Finset.Icc 6 22).card := Finset.card_le_card hsubset
    _ = 17 := by norm_num

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











/-! ## The literal smooth donor window -/

















private theorem yNat_tendsto_atTop_BankOrdinaryDonorSupply :
    Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
      tendsto_natCast_atTop_atTop
  exact tendsto_nat_floor_atTop.comp hy



/-! ## Summing one-donor prime intervals -/









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















/-! ## Marker supply from the exact fiber bound -/











/-! ## The five fixed nonbottom scales -/

private theorem natDiv_fixed_endpoint_ratio_tendsto
    {m : ℕ → ℕ} {a : ℝ}
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ))
      atTop (nhds a)) (u : ℕ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ ((m n / u : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a / (u : ℝ))) := by
  have hmain := hm.div_const (u : ℝ)
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ))
      atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hlower : Tendsto
      (fun n : ℕ ↦ ((m n : ℝ) / (n : ℝ)) / (u : ℝ) -
        1 / (n : ℝ)) atTop (nhds (a / (u : ℝ))) := by
    simpa only [sub_zero] using hmain.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hmain
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hfloor := realDiv_sub_one_lt_cast_natDiv (m n) u hu
    calc
      ((m n : ℝ) / (n : ℝ)) / (u : ℝ) - 1 / (n : ℝ) =
          ((m n : ℝ) / (u : ℝ) - 1) / (n : ℝ) := by
            field_simp
      _ ≤ ((m n / u : ℕ) : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hfloor.le hnR.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      ((m n / u : ℕ) : ℝ) / (n : ℝ) ≤
          ((m n : ℝ) / (u : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right (cast_natDiv_le_realDiv (m n) u) hnR.le
      _ = ((m n : ℝ) / (n : ℝ)) / (u : ℝ) := by
        field_simp

private theorem twoNat_ratio_tendsto :
    Tendsto (fun n : ℕ ↦ ((2 * n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  push_cast
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']

private theorem upperEndpoint_ratio_tendsto_two
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦
      (upperEndpoint n (upperTailLength c n) : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
  have h := (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (2 : ℝ))
      atTop (nhds 2)).add (upperTailLength_ratio_tendsto_zero hc)
  have h' : Tendsto
      (fun n : ℕ ↦ 2 + (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
    simpa only [add_zero] using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']

private theorem fixedDonor_gap_normalized_tendsto
    {c : ℝ} (hc : 0 < c) {u : ℕ} (hu : 0 < u) :
    Tendsto
      (fun n : ℕ ↦
        (((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ)) / secondOrderScale n)
      atTop (nhds (c / (u : ℝ))) := by
  have hmain := (upperTailLength_normalized_tendsto hc).div_const (u : ℝ)
  have hinv : Tendsto (fun n : ℕ ↦ 1 / secondOrderScale n)
      atTop (nhds 0) := by
    simpa only [one_div] using secondOrderScale_tendsto_atTop.inv_tendsto_atTop
  have hlower : Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) /
        secondOrderScale n / (u : ℝ) - 1 / secondOrderScale n)
      atTop (nhds (c / (u : ℝ))) := by
    simpa only [sub_zero] using hmain.sub hinv
  have hupper : Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) /
        secondOrderScale n / (u : ℝ) + 1 / secondOrderScale n)
      atTop (nhds (c / (u : ℝ))) := by
    simpa only [add_zero] using hmain.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hMlower := realDiv_sub_one_lt_cast_natDiv
      (upperEndpoint n (upperTailLength c n)) u hu
    have hNupper := cast_natDiv_le_realDiv (2 * n) u
    rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hMlower
    have hnum : (upperTailLength c n : ℝ) / (u : ℝ) - 1 ≤
        ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ) := by
      calc
        (upperTailLength c n : ℝ) / (u : ℝ) - 1 =
            ((2 * (n : ℝ) + upperTailLength c n) / (u : ℝ) - 1) -
              (2 * (n : ℝ)) / (u : ℝ) := by ring
        _ ≤ ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
              (((2 * n) / u : ℕ) : ℝ) := by
          apply sub_le_sub hMlower.le
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hNupper
    calc
      (upperTailLength c n : ℝ) / secondOrderScale n / (u : ℝ) -
          1 / secondOrderScale n =
        ((upperTailLength c n : ℝ) / (u : ℝ) - 1) /
          secondOrderScale n := by field_simp
      _ ≤ (((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ)) / secondOrderScale n :=
        div_le_div_of_nonneg_right hnum hscale.le
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hMupper := cast_natDiv_le_realDiv
      (upperEndpoint n (upperTailLength c n)) u
    have hNlower := realDiv_sub_one_lt_cast_natDiv (2 * n) u hu
    rw [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hMupper
    have hnum :
        ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
            (((2 * n) / u : ℕ) : ℝ) ≤
          (upperTailLength c n : ℝ) / (u : ℝ) + 1 := by
      calc
        ((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
            (((2 * n) / u : ℕ) : ℝ) ≤
          (2 * (n : ℝ) + upperTailLength c n) / (u : ℝ) -
            ((2 * (n : ℝ)) / (u : ℝ) - 1) := by
          apply sub_le_sub hMupper
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hNlower.le
        _ = (upperTailLength c n : ℝ) / (u : ℝ) + 1 := by ring
    calc
      (((upperEndpoint n (upperTailLength c n) / u : ℕ) : ℝ) -
          (((2 * n) / u : ℕ) : ℝ)) / secondOrderScale n ≤
        ((upperTailLength c n : ℝ) / (u : ℝ) + 1) /
          secondOrderScale n :=
        div_le_div_of_nonneg_right hnum hscale.le
      _ = (upperTailLength c n : ℝ) / secondOrderScale n / (u : ℝ) +
          1 / secondOrderScale n := by field_simp

/-- At any fixed donor, the exact product interval contains asymptotically
`(c/u)n/log(n)^2` primes. -/
theorem bankOrdinaryPrimeChoices_fixedDonor_normalized_tendsto
    {c : ℝ} (hc : 0 < c) {u : ℕ} (hu : 0 < u) :
    Tendsto
      (fun n : ℕ ↦
        ((bankOrdinaryPrimeChoices n
          (upperEndpoint n (upperTailLength c n)) u).card : ℝ) /
            SafePrimeCounting.shortIntervalPrimeScale n)
      atTop (nhds (c / (u : ℝ))) := by
  have hlower := natDiv_fixed_endpoint_ratio_tendsto
    twoNat_ratio_tendsto u hu
  have hupper := natDiv_fixed_endpoint_ratio_tendsto
    (upperEndpoint_ratio_tendsto_two hc) u hu
  have hgap := fixedDonor_gap_normalized_tendsto hc hu
  have horder : ∀ᶠ n : ℕ in atTop,
      (2 * n) / u ≤ upperEndpoint n (upperTailLength c n) / u :=
    Eventually.of_forall fun n ↦
      Nat.div_le_div_right (two_mul_le_upperEndpoint n (upperTailLength c n))
  simpa only [bankOrdinaryPrimeChoices, bankPrimeInterval] using
    SafePrimeCounting.prime_Ioc_shortMovingInterval_normalized_tendsto
      (div_pos (by norm_num) (by exact_mod_cast hu)) hlower hupper hgap horder

private theorem eventually_smallPrimeChoice_pairs_eligible
    {c : ℝ} (hc : 0 < c) (scale : SmallDescentScale) :
    ∀ᶠ n : ℕ in atTop, ∀ P ∈
      bankOrdinaryPrimeChoices n
        (upperEndpoint n (upperTailLength c n))
        (bankOrdinarySmallDonor scale),
      (P, bankOrdinarySmallDonor scale) ∈
        bankOrdinaryEligibleRelation n
          (upperEndpoint n (upperTailLength c n))
          (smallDescentScaleValue scale) := by
  have hY : ∀ᶠ n : ℕ in atTop, 23 ≤ yNat n :=
    yNat_tendsto_atTop_BankOrdinaryDonorSupply.eventually (eventually_ge_atTop 23)
  have htail : ∀ᶠ n : ℕ in atTop,
      2 * (smallDescentScaleValue scale : ℝ) *
          (upperTailLength c n : ℝ) ≤
        (3 * (bankOrdinarySmallDonor scale : ℝ) -
          4 * (smallDescentScaleValue scale : ℝ)) * (n : ℝ) := by
    have hmargin : 0 <
        3 * (bankOrdinarySmallDonor scale : ℝ) -
          4 * (smallDescentScaleValue scale : ℝ) := by
      cases scale <;>
        norm_num [bankOrdinarySmallDonor, smallDescentScaleValue,
          smallDescentScaleNumerator, smallDescentScaleDenominator]
    have hscaleValue : 0 < (smallDescentScaleValue scale : ℝ) := by
      cases scale <;>
        norm_num [smallDescentScaleValue, smallDescentScaleNumerator,
          smallDescentScaleDenominator]
    have hden : 0 < 2 * (smallDescentScaleValue scale : ℝ) := by positivity
    have hratio := (upperTailLength_ratio_tendsto_zero hc).eventually
      (eventually_lt_nhds (div_pos hmargin hden))
    filter_upwards [hratio, eventually_gt_atTop 0] with n hn hnpos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hlt : (upperTailLength c n : ℝ) <
        ((3 * (bankOrdinarySmallDonor scale : ℝ) -
            4 * (smallDescentScaleValue scale : ℝ)) * (n : ℝ)) /
          (2 * (smallDescentScaleValue scale : ℝ)) := by
      calc
        (upperTailLength c n : ℝ) =
            ((upperTailLength c n : ℝ) / (n : ℝ)) * (n : ℝ) := by
              field_simp [hnR.ne']
        _ < ((3 * (bankOrdinarySmallDonor scale : ℝ) -
              4 * (smallDescentScaleValue scale : ℝ)) /
              (2 * (smallDescentScaleValue scale : ℝ))) *
              (n : ℝ) := mul_lt_mul_of_pos_right hn hnR
        _ = ((3 * (bankOrdinarySmallDonor scale : ℝ) -
              4 * (smallDescentScaleValue scale : ℝ)) * (n : ℝ)) /
              (2 * (smallDescentScaleValue scale : ℝ)) := by
                field_simp [hden.ne']
    have hmul := (lt_div_iff₀ hden).mp hlt
    nlinarith
  filter_upwards [hY, htail] with n hYn htailn
  intro P hP
  have huPos := bankOrdinarySmallDonor_pos scale
  have hscaleValue : 0 < (smallDescentScaleValue scale : ℝ) := by
    cases scale <;>
      norm_num [smallDescentScaleValue, smallDescentScaleNumerator,
        smallDescentScaleDenominator]
  have hPData := (mem_bankOrdinaryPrimeChoices huPos).mp hP
  apply bankOrdinarySmallPair_mem_eligible scale hYn hPData.1
  · unfold InOrdinaryBankMarkerInterval
    have hwindow := bankOrdinarySmallDonor_mem_window scale
    have htailLowerQ :
        2 * (n : ℝ) < (P : ℝ) *
          (bankOrdinarySmallDonor scale : ℝ) := by
      exact_mod_cast hPData.2.1
    have htailUpperQ :
        (P : ℝ) * (bankOrdinarySmallDonor scale : ℝ) ≤
          upperEndpoint n (upperTailLength c n) := by
      exact_mod_cast hPData.2.2
    have hwindowLower :
        4 * (smallDescentScaleValue scale : ℝ) ≤
          3 * (bankOrdinarySmallDonor scale : ℝ) := by
      exact_mod_cast hwindow.1
    have hwindowUpper :
        2 * (bankOrdinarySmallDonor scale : ℝ) ≤
          3 * (smallDescentScaleValue scale : ℝ) := by
      exact_mod_cast hwindow.2
    have hMcast :
        (upperEndpoint n (upperTailLength c n) : ℝ) =
          2 * (n : ℝ) + upperTailLength c n := by
      simp [upperEndpoint]
    constructor
    · have hPnonneg : (0 : ℝ) ≤ P := by positivity
      have hwindowUpperP :=
        mul_le_mul_of_nonneg_right hwindowUpper hPnonneg
      have htailTwice := mul_lt_mul_of_pos_left htailLowerQ
        (by norm_num : (0 : ℝ) < 2)
      have hreal : 4 * (n : ℝ) <
          3 * (smallDescentScaleValue scale : ℝ) * (P : ℝ) := by
        calc
          4 * (n : ℝ) = 2 * (2 * (n : ℝ)) := by ring
          _ < 2 * ((P : ℝ) * bankOrdinarySmallDonor scale) := htailTwice
          _ ≤ 3 * smallDescentScaleValue scale * (P : ℝ) := by
            ring_nf at hwindowUpperP ⊢
            exact hwindowUpperP
      exact_mod_cast hreal
    · rw [hMcast] at htailUpperQ
      have hscaledTail := mul_le_mul_of_nonneg_left htailUpperQ
        (show (0 : ℝ) ≤ 2 * smallDescentScaleValue scale by positivity)
      have huR : (0 : ℝ) < bankOrdinarySmallDonor scale := by
        exact_mod_cast huPos
      have hmul :
          (2 * smallDescentScaleValue scale * (P : ℝ)) *
              bankOrdinarySmallDonor scale ≤
            (3 * (n : ℝ)) * bankOrdinarySmallDonor scale := by
        ring_nf at hscaledTail htailn ⊢
        nlinarith
      have hcancel :
          2 * (smallDescentScaleValue scale : ℝ) * (P : ℝ) ≤
            3 * (n : ℝ) := le_of_mul_le_mul_right hmul huR
      exact_mod_cast hcancel
  · exact hPData.2.1
  · exact hPData.2.2



/-- The fixed donor at each small scale also gives distinct actual markers.
This is the marker-count form needed by the request allocation: no division
by a donor-multiplicity estimate is needed because the displayed donor is
fixed and the prime coordinate itself is the marker. -/
theorem bankOrdinary_smallScale_markerCount_lower
    {c : ℝ} (hc : 0 < c) (scale : SmallDescentScale) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ᶠ n : ℕ in atTop,
        rho * secondOrderScale n / Real.log (n : ℝ) ≤
          (bankEligibleMarkerCount
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n))
              (smallDescentScaleValue scale)) : ℝ) := by
  let rho : ℝ := c / (2 * bankOrdinarySmallDonor scale)
  have hrho : 0 < rho := by
    dsimp only [rho]
    have huR : (0 : ℝ) < bankOrdinarySmallDonor scale := by
      exact_mod_cast bankOrdinarySmallDonor_pos scale
    exact div_pos hc (mul_pos (by norm_num) huR)
  refine ⟨rho, hrho, ?_⟩
  have hlimit := bankOrdinaryPrimeChoices_fixedDonor_normalized_tendsto
    hc (bankOrdinarySmallDonor_pos scale)
  have hlower : ∀ᶠ n : ℕ in atTop,
      c / (2 * bankOrdinarySmallDonor scale) ≤
        ((bankOrdinaryPrimeChoices n
          (upperEndpoint n (upperTailLength c n))
          (bankOrdinarySmallDonor scale)).card : ℝ) /
            SafePrimeCounting.shortIntervalPrimeScale n :=
    hlimit.eventually (eventually_ge_nhds (by
      have hu : (0 : ℝ) < bankOrdinarySmallDonor scale := by
        exact_mod_cast bankOrdinarySmallDonor_pos scale
      have : c / (2 * (bankOrdinarySmallDonor scale : ℝ)) <
          c / (bankOrdinarySmallDonor scale : ℝ) := by
        calc
          c / (2 * (bankOrdinarySmallDonor scale : ℝ)) =
              (c / (bankOrdinarySmallDonor scale : ℝ)) / 2 := by
                field_simp [hu.ne']
          _ < c / (bankOrdinarySmallDonor scale : ℝ) :=
            half_lt_self (div_pos hc hu)
      exact this))
  have heligible := eventually_smallPrimeChoice_pairs_eligible hc scale
  filter_upwards [hlower, heligible, eventually_secondOrderScale_pos,
      eventually_gt_atTop 2] with n hprime helig hscale hn
  have hlogN : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hshortPos : 0 < SafePrimeCounting.shortIntervalPrimeScale n :=
    by
      rw [SafePrimeCounting.shortIntervalPrimeScale]
      exact div_pos hscale hlogN
  have hprimeLower : rho * secondOrderScale n / Real.log (n : ℝ) ≤
      ((bankOrdinaryPrimeChoices n
        (upperEndpoint n (upperTailLength c n))
        (bankOrdinarySmallDonor scale)).card : ℝ) := by
    have hmul := (le_div_iff₀ hshortPos).mp hprime
    dsimp only [rho]
    simpa only [SafePrimeCounting.shortIntervalPrimeScale, mul_div_assoc] using hmul
  have hsubset :
      bankOrdinaryPrimeChoices n
          (upperEndpoint n (upperTailLength c n))
          (bankOrdinarySmallDonor scale) ⊆
        bankEligibleMarkers
          (bankOrdinaryEligibleRelation n
            (upperEndpoint n (upperTailLength c n))
            (smallDescentScaleValue scale)) := by
    intro P hP
    rw [bankEligibleMarkers, Finset.mem_image]
    exact ⟨(P, bankOrdinarySmallDonor scale), helig P hP, rfl⟩
  have hcard := Finset.card_le_card hsubset
  exact hprimeLower.trans (by exact_mod_cast hcard)

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



/-- Exact demand in one scale/orientation fiber.  Fixing the orientation
leaves exactly `beta_p` signed copies for every prime. -/
theorem bankOrdinaryPoolDemand_eq
    (n : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankOrdinaryPoolDemand n pool =
      ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p *
          (bankOrdinaryCoreSourcesAtScale p pool.1).card := by
  rw [bankOrdinaryPoolDemand, ← Fintype.card_coe]
  rw [Fintype.card_congr (bankOrdinaryPaperRequestFiberEquiv n pool),
    Fintype.card_sigma]
  change (∑ p : bankRoundingPrimeSupport n,
    Fintype.card (Fin (bankRoundingBeta n p) ×
      bankOrdinaryCoreSourcesAtScale p pool.1)) = _
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  simpa only using
    (Finset.sum_attach (bankRoundingPrimeSupport n) (fun p ↦
      bankRoundingBeta n p *
        (bankOrdinaryCoreSourcesAtScale p pool.1).card))

private theorem bankOrdinaryCoreSourcesAtScale_card_le_seventeen_of_prime
    {p j : ℕ} (hp : p.Prime) (hj : j ≤ 5) :
    (bankOrdinaryCoreSourcesAtScale p j).card ≤ 17 := by
  by_cases hp5 : p ≤ 5
  · simp [bankOrdinaryCoreSourcesAtScale,
      bankOrdinaryCoreSources_of_le_five hp5]
  · exact bankOrdinaryCoreSourcesAtSmallScale_card_le
      (by omega) (prime_not_isPowerOfTwo_of_five_le hp (by omega)) hj

private theorem bankOrdinaryCoreSourcesAtScale_card_le_two_of_prime
    {p j : ℕ} (hp : p.Prime) (hj : 6 ≤ j) :
    (bankOrdinaryCoreSourcesAtScale p j).card ≤ 2 := by
  by_cases hp5 : p ≤ 5
  · simp [bankOrdinaryCoreSourcesAtScale,
      bankOrdinaryCoreSources_of_le_five hp5]
  · exact bankOrdinaryCoreSourcesAtLargeScale_card_le_two
      (by omega) (prime_not_isPowerOfTwo_of_five_le hp (by omega)) hj

/-- Literal small-table demand bound for either orientation. -/
theorem bankOrdinaryPoolDemand_le_seventeen_beta
    (n : ℕ) (pool : BankOrdinaryOrientationPool) (hpool : pool.1 ≤ 5) :
    bankOrdinaryPoolDemand n pool ≤ 17 * bankBottomPaperDemand n := by
  rw [bankOrdinaryPoolDemand_eq, bankBottomPaperDemand]
  calc
    (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p *
          (bankOrdinaryCoreSourcesAtScale p pool.1).card) ≤
      ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p * 17 := by
          apply Finset.sum_le_sum
          intro p hp
          exact Nat.mul_le_mul_left _
            (bankOrdinaryCoreSourcesAtScale_card_le_seventeen_of_prime
              (bankRoundingPrimeSupport_prime hp) hpool)
    _ = (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p) * 17 := by
          rw [Finset.sum_mul]
    _ = 17 * ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p := by omega

/-- Sharp large-grid demand bound for either orientation. -/
theorem bankOrdinaryPoolDemand_le_two_beta
    (n : ℕ) (pool : BankOrdinaryOrientationPool) (hpool : 6 ≤ pool.1) :
    bankOrdinaryPoolDemand n pool ≤ 2 * bankBottomPaperDemand n := by
  rw [bankOrdinaryPoolDemand_eq, bankBottomPaperDemand]
  calc
    (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p *
          (bankOrdinaryCoreSourcesAtScale p pool.1).card) ≤
      ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p * 2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact Nat.mul_le_mul_left _
            (bankOrdinaryCoreSourcesAtScale_card_le_two_of_prime
              (bankRoundingPrimeSupport_prime hp) hpool)
    _ = (∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p) * 2 := by
          rw [Finset.sum_mul]
    _ = 2 * ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p := by omega

theorem bankOrdinaryPoolDemand_scale_zero (n : ℕ)
    (orientation : BankBottomOrientation) :
    bankOrdinaryPoolDemand n (0, orientation) = 0 := by
  rw [bankOrdinaryPoolDemand_eq]
  apply Finset.sum_eq_zero
  intro p hp
  apply Nat.mul_eq_zero.mpr
  right
  apply Finset.card_eq_zero.mpr
  rw [bankOrdinaryCoreSourcesAtScale]
  apply Finset.filter_eq_empty_iff.mpr
  intro source hsource hsourceScale
  have hpPrime := bankRoundingPrimeSupport_prime hp
  have hp5 : 5 ≤ p := by
    by_contra hpSmall
    have hpLe : p ≤ 5 := by omega
    rw [bankOrdinaryCoreSources_of_le_five hpLe] at hsource
    simp at hsource
  have hpPower := prime_not_isPowerOfTwo_of_five_le hpPrime hp5
  have hspec := bankOrdinaryCoreSource_spec hp5 hpPower hsource
  have hpositive := one_le_bankOrdinaryComponentScaleIndex hspec.1
  omega

theorem bankOrdinaryPoolDemand_zero_of_scale_gt_yNat
    {n : ℕ} {pool : BankOrdinaryOrientationPool}
    (hscale : (yNat n : ℚ) < bankOrdinaryScale pool.1) :
    bankOrdinaryPoolDemand n pool = 0 := by
  rw [bankOrdinaryPoolDemand_eq]
  apply Finset.sum_eq_zero
  intro p hp
  apply Nat.mul_eq_zero.mpr
  right
  apply Finset.card_eq_zero.mpr
  rw [bankOrdinaryCoreSourcesAtScale]
  apply Finset.filter_eq_empty_iff.mpr
  intro source hsource hsourceScale
  have hsourcePrime := bankRoundingPrimeSupport_prime hp
  have hp5 : 5 ≤ p := by
    by_contra hpSmall
    have hpLe : p ≤ 5 := by omega
    exact (by
      rw [bankOrdinaryCoreSources_of_le_five hpLe] at hsource
      simp at hsource)
  have hpPower := prime_not_isPowerOfTwo_of_five_le hsourcePrime hp5
  have hspec := bankOrdinaryCoreSource_spec hp5 hpPower hsource
  have hsourceLe := bankOrdinaryCoreSource_le_start hsource
  have hpY := bankRoundingPrimeSupport_le_yNat hp
  have hscaleLt : bankOrdinaryScale pool.1 < (source : ℚ) := by
    rw [← hsourceScale]
    exact hspec.2.2.2.2.2.2.1.1
  have hsourceY : source ≤ yNat n := hsourceLe.trans hpY
  exact (not_lt_of_ge (by exact_mod_cast hsourceY))
    (hscale.trans hscaleLt)

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

private theorem yNat_isLittleO_bankOrdinaryWorstMarkerScale :
    (fun n : ℕ ↦ (yNat n : ℝ)) =o[atTop]
      bankOrdinaryWorstMarkerScale := by
  apply (isLittleO_iff_tendsto' ?_).mpr
    yNat_div_bankOrdinaryWorstMarkerScale_tendsto_zero
  filter_upwards [eventually_gt_atTop 2] with n hn hzero
  have hscale : 0 < bankOrdinaryWorstMarkerScale n := by
    rw [bankOrdinaryWorstMarkerScale]
    exact div_pos (secondOrderScale_pos (by omega)) (by positivity)
  exact (hscale.ne' hzero).elim

/-- The beta reserve itself, in the little-o form used for ordinary pools. -/
theorem bankBottomPaperDemand_isLittleO_bankOrdinaryWorstMarkerScale :
    (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =o[atTop]
      bankOrdinaryWorstMarkerScale :=
  bankBottomPaperDemand_isBigO_yNat.trans_isLittleO
    yNat_isLittleO_bankOrdinaryWorstMarkerScale

/-- Uniform analytic terminal for ordinary demand: the common beta reserve is
little-o of the worst marker lower bound among all moving grid scales. -/
theorem bankBottomPaperDemand_div_bankOrdinaryWorstMarkerScale_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomPaperDemand n : ℝ) /
          bankOrdinaryWorstMarkerScale n)
      atTop (nhds 0) :=
  bankBottomPaperDemand_isLittleO_bankOrdinaryWorstMarkerScale.tendsto_div_nhds_zero







/-- Uniform comparison of the denominator in the analytic marker lower bound
with `yNat`.  The factor five comes directly from the audited lower bound on
`log(yNat)`. -/
theorem eventually_bankOrdinary_max_scale_log_le_five_yNat :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
      Q ≤ (yNat n : ℚ) →
        max (Q : ℝ) (Real.log (n : ℝ)) ≤
          5 * max 1 (yNat n : ℝ) := by
  filter_upwards [eventually_gt_atTop 2,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
      with n hn hlogY
  intro Q hQ
  have hyPos : 0 < (yNat n : ℝ) := by
    have hLPos : 0 < L n := L_pos (by omega)
    have : 0 < Real.log (yNat n : ℝ) := by nlinarith
    exact (show (0 : ℝ) < 1 by norm_num).trans
      ((Real.log_pos_iff (Nat.cast_nonneg _)).mp this)
  have hlogLe : Real.log (yNat n : ℝ) ≤ yNat n := by
    have h := Real.log_le_sub_one_of_pos hyPos
    linarith
  have hLLe : Real.log (n : ℝ) ≤ 5 * (yNat n : ℝ) := by
    rw [← show L n = Real.log (n : ℝ) by rfl]
    nlinarith
  have hQR : (Q : ℝ) ≤ yNat n := by exact_mod_cast hQ
  apply max_le
  · exact hQR.trans (by
      have : (0 : ℝ) ≤ yNat n := hyPos.le
      exact le_trans (le_mul_of_one_le_left this (by norm_num))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)))
  · exact hLLe.trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryPoolMatching -/
section


/-!
# Actual matching of ordinary requests to marker--donor pairs

At every grid scale the selected marker--donor pairs are split by
`BankMarkerDonorCombinatorics` into the two path orientations.  The marker
intervals of distinct geometric scales are disjoint, so these are genuinely
disjoint pools of numerical pairs, not merely scale-tagged copies.

The beta-demand estimates are compared with the large moving marker lower
bound and the five fixed small-scale marker lower bounds.  Pointwise finite
embeddings then give one globally injective assignment from every actual
ordinary component request to an actual eligible marker--donor pair.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Actual oriented occurrence pools -/







theorem bankOrdinaryPoolCapacity_ge_half_markerCount
    (n M : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankEligibleMarkerCount
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1)) / 2 ≤
      bankOrdinaryPoolCapacity n M pool := by
  cases pool with
  | mk j orientation =>
      cases orientation
      · rw [bankOrdinaryPoolCapacity, bankOrdinaryAvailablePairs,
          card_bankOrientationPoolFirst, card_bankMarkerDonorPairs]
      · have hbalanced := (bankOrientationPools_card_balanced
            (bankOrdinaryEligibleRelation n M (bankOrdinaryScale j))).1
        rw [card_bankOrientationPoolFirst, card_bankMarkerDonorPairs]
          at hbalanced
        simpa only [bankOrdinaryPoolCapacity,
          bankOrdinaryAvailablePairs] using hbalanced







/-! ## Capacity from the beta reserve -/

private theorem demand_le_half_of_two_mul_le
    {d K : ℕ} (h : 2 * d ≤ K) : d ≤ K / 2 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  simpa only [Nat.mul_comm] using h

private theorem eventually_bankOrdinary_smallPoolDemand_le_capacity
    {c : ℝ} (hc : 0 < c) (scale : SmallDescentScale)
    (orientation : BankBottomOrientation) :
    ∀ᶠ n : ℕ in atTop,
      bankOrdinaryPoolDemand n
          (smallDescentScaleIndex scale, orientation) ≤
        bankOrdinaryPoolCapacity n
          (upperEndpoint n (upperTailLength c n))
          (smallDescentScaleIndex scale, orientation) := by
  obtain ⟨rho, hrho, hmarkers⟩ :=
    bankOrdinary_smallScale_markerCount_lower hc scale
  have hratio :=
    bankBottomPaperDemand_div_bankBottomPrimeScale_tendsto_zero
  have hsmall := hratio.eventually
    (eventually_lt_nhds (div_pos hrho (by norm_num : (0 : ℝ) < 34)))
  filter_upwards [hmarkers, hsmall, eventually_gt_atTop 2,
      eventually_secondOrderScale_pos] with n hmarker hbeta hn hsecond
  let pool : BankOrdinaryOrientationPool :=
    (smallDescentScaleIndex scale, orientation)
  let eligible := bankOrdinaryEligibleRelation n
    (upperEndpoint n (upperTailLength c n))
    (bankOrdinaryScale (smallDescentScaleIndex scale))
  let K := bankEligibleMarkerCount eligible
  have hdemand := bankOrdinaryPoolDemand_le_seventeen_beta n pool
    (smallDescentScaleIndex_le_five scale)
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hprimeScale : 0 < bankBottomPrimeScale n := by
    rw [bankBottomPrimeScale, SafePrimeCounting.shortIntervalPrimeScale]
    exact div_pos hsecond hlog
  have hbetaMul :
      (34 : ℝ) * bankBottomPaperDemand n <
        rho * bankBottomPrimeScale n := by
    have := (div_lt_iff₀ hprimeScale).mp hbeta
    nlinarith
  have hmarker' : rho * bankBottomPrimeScale n ≤ (K : ℝ) := by
    dsimp only [K, eligible]
    rw [← smallDescentScaleValue_eq_bankOrdinaryScale]
    simpa only [bankBottomPrimeScale,
      SafePrimeCounting.shortIntervalPrimeScale, mul_div_assoc] using hmarker
  have htwoDemand : 2 * bankOrdinaryPoolDemand n pool ≤ K := by
    have hdemandR :
        ((2 * bankOrdinaryPoolDemand n pool : ℕ) : ℝ) < (K : ℝ) := by
      have hdemandCast : (bankOrdinaryPoolDemand n pool : ℝ) ≤
          17 * bankBottomPaperDemand n := by exact_mod_cast hdemand
      push_cast
      nlinarith [hbetaMul, hmarker']
    exact_mod_cast hdemandR.le
  exact (demand_le_half_of_two_mul_le htwoDemand).trans
    (bankOrdinaryPoolCapacity_ge_half_markerCount n
      (upperEndpoint n (upperTailLength c n)) pool)

private theorem eventually_bankOrdinary_allSmallPoolDemands_le_capacity
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∀ scale : SmallDescentScale, ∀ orientation : BankBottomOrientation,
        bankOrdinaryPoolDemand n
            (smallDescentScaleIndex scale, orientation) ≤
          bankOrdinaryPoolCapacity n
            (upperEndpoint n (upperTailLength c n))
            (smallDescentScaleIndex scale, orientation) := by
  rw [Filter.eventually_all]
  intro scale
  rw [Filter.eventually_all]
  exact eventually_bankOrdinary_smallPoolDemand_le_capacity hc scale

private theorem eventually_bankOrdinary_largePoolDemands_le_capacity
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ, 6 ≤ j → ∀ orientation : BankBottomOrientation,
        bankOrdinaryPoolDemand n (j, orientation) ≤
          bankOrdinaryPoolCapacity n
            (upperEndpoint n (upperTailLength c n)) (j, orientation) := by
  obtain ⟨rho, hrho, hmarkers⟩ :=
    exists_eventually_bankOrdinary_markerCount_lower hc
  have hratio :=
    bankBottomPaperDemand_div_bankOrdinaryWorstMarkerScale_tendsto_zero
  have hsmall := hratio.eventually
    (eventually_lt_nhds (div_pos hrho (by norm_num : (0 : ℝ) < 20)))
  filter_upwards [hmarkers, hsmall,
      eventually_bankOrdinary_max_scale_log_le_five_yNat,
      eventually_gt_atTop 3, eventually_secondOrderScale_pos]
      with n hmarker hbeta hmax hn hsecond
  intro j hj orientation
  let pool : BankOrdinaryOrientationPool := (j, orientation)
  let Q : ℚ := bankOrdinaryScale j
  by_cases hQY : Q ≤ (yNat n : ℚ)
  · have hQ20 : (20 : ℚ) < Q :=
      twenty_lt_bankOrdinaryScale_of_six_le hj
    have hdemand := bankOrdinaryPoolDemand_le_two_beta n pool hj
    have hmarkerN := hmarker Q hQ20 hQY
    let eligible := bankOrdinaryEligibleRelation n
      (upperEndpoint n (upperTailLength c n)) Q
    let K := bankEligibleMarkerCount eligible
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hyMax : 0 < max 1 (yNat n : ℝ) := by positivity
    have hworst : 0 < bankOrdinaryWorstMarkerScale n := by
      rw [bankOrdinaryWorstMarkerScale]
      exact div_pos hsecond hyMax
    have hbetaMul :
        (20 : ℝ) * bankBottomPaperDemand n <
          rho * bankOrdinaryWorstMarkerScale n := by
      have := (div_lt_iff₀ hworst).mp hbeta
      nlinarith
    have hmaxN := hmax Q hQY
    have hdenomPos :
        0 < max (Q : ℝ) (Real.log (n : ℝ)) := by
      have hQposQ : (0 : ℚ) < Q := by linarith
      have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQposQ
      exact hQpos.trans_le (le_max_left _ _)
    have hworstCompare :
        rho / 5 * bankOrdinaryWorstMarkerScale n ≤
          rho * secondOrderScale n /
            max (Q : ℝ) (Real.log (n : ℝ)) := by
      rw [bankOrdinaryWorstMarkerScale]
      field_simp [hyMax.ne', hdenomPos.ne']
      nlinarith [hmaxN, mul_pos hrho hsecond]
    have htwoDemand : 2 * bankOrdinaryPoolDemand n pool ≤ K := by
      have htwoDemandR :
          ((2 * bankOrdinaryPoolDemand n pool : ℕ) : ℝ) < (K : ℝ) := by
        have hdemandR :
            (bankOrdinaryPoolDemand n pool : ℝ) ≤
              2 * bankBottomPaperDemand n := by exact_mod_cast hdemand
        have hbetaR :
            4 * (bankBottomPaperDemand n : ℝ) <
              rho / 5 * bankOrdinaryWorstMarkerScale n := by
          nlinarith
        have hmarkerR :
            rho * secondOrderScale n /
                max (Q : ℝ) (Real.log (n : ℝ)) ≤ (K : ℝ) := by
          simpa only [K, eligible, Q] using hmarkerN
        push_cast
        calc
          2 * (bankOrdinaryPoolDemand n pool : ℝ) ≤
              4 * (bankBottomPaperDemand n : ℝ) := by
            nlinarith
          _ < rho / 5 * bankOrdinaryWorstMarkerScale n := hbetaR
          _ ≤ rho * secondOrderScale n /
              max (Q : ℝ) (Real.log (n : ℝ)) := hworstCompare
          _ ≤ (K : ℝ) := hmarkerR
      exact_mod_cast htwoDemandR.le
    exact (demand_le_half_of_two_mul_le htwoDemand).trans
      (bankOrdinaryPoolCapacity_ge_half_markerCount n
        (upperEndpoint n (upperTailLength c n)) pool)
  · have hdemandZero : bankOrdinaryPoolDemand n pool = 0 :=
      bankOrdinaryPoolDemand_zero_of_scale_gt_yNat
        (lt_of_not_ge hQY)
    rw [hdemandZero]
    exact Nat.zero_le _

/-- All ordinary grid-scale capacity inequalities hold simultaneously. -/
theorem eventually_bankOrdinary_allPoolDemands_le_capacity
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ pool : BankOrdinaryOrientationPool,
      bankOrdinaryPoolDemand n pool ≤
        bankOrdinaryPoolCapacity n
          (upperEndpoint n (upperTailLength c n)) pool := by
  filter_upwards [eventually_bankOrdinary_allSmallPoolDemands_le_capacity hc,
      eventually_bankOrdinary_largePoolDemands_le_capacity hc]
      with n hsmall hlarge
  rintro ⟨j, orientation⟩
  by_cases hj0 : j = 0
  · subst j
    rw [bankOrdinaryPoolDemand_scale_zero]
    exact Nat.zero_le _
  · by_cases hj5 : j ≤ 5
    · interval_cases j
      · exact (hj0 rfl).elim
      · simpa [smallDescentScaleIndex] using hsmall .one orientation
      · simpa [smallDescentScaleIndex] using hsmall .two orientation
      · simpa [smallDescentScaleIndex] using hsmall .three orientation
      · simpa [smallDescentScaleIndex] using hsmall .four orientation
      · simpa [smallDescentScaleIndex] using hsmall .five orientation
    · exact hlarge j (by omega) orientation

/-! ## Finite poolwise matching -/



private theorem bankOrdinaryPoolMatching_nonempty
    (n M : ℕ)
    (hcapacity : ∀ pool : BankOrdinaryOrientationPool,
      bankOrdinaryPoolDemand n pool ≤ bankOrdinaryPoolCapacity n M pool) :
    Nonempty (BankOrdinaryPoolMatching n M) := by
  let embedding : (pool : BankOrdinaryOrientationPool) →
      ↑(bankOrdinaryRequestsInPool n pool) ↪
        ↑(bankOrdinaryAvailablePairs n M pool) := fun pool ↦
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_coe, bankOrdinaryPoolDemand,
        bankOrdinaryPoolCapacity] using hcapacity pool))
  exact ⟨⟨embedding⟩⟩























/-- Terminal ordinary allocation: every actual signed-copy/component request
receives a globally distinct actual eligible marker--donor pair in its exact
scale and orientation pool. -/
theorem eventually_exists_bankOrdinaryPaper_injective_assignment
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ matching : BankOrdinaryPoolMatching n
          (upperEndpoint n (upperTailLength c n)),
        Function.Injective matching.matchedPair ∧
          ∀ request : ↑(bankOrdinaryPaperRequests n),
            matching.matchedPair request ∈
              bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n))
                (bankOrdinaryScale
                  (bankOrdinaryPaperRequestPool n request.1).1) := by
  filter_upwards [eventually_bankOrdinary_allPoolDemands_le_capacity hc]
      with n hcapacity
  let matching := Classical.choice
    (bankOrdinaryPoolMatching_nonempty n
      (upperEndpoint n (upperTailLength c n)) hcapacity)
  exact ⟨matching, matching.matchedPair_injective,
    matching.matchedPair_eligible⟩

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

/-- A prime path has at most `p` nonterminal component sources.  This coarse
bound is deliberately independent of the geometric-cell congestion bounds:
it is the convenient global estimate used when every ordinary marker is
guarded at once. -/
theorem bankOrdinaryPrimeCoreSources_card_le
    {p : ℕ} (hp : p.Prime) :
    (bankOrdinaryCoreSources p).card ≤ p := by
  by_cases hp5 : p ≤ 5
  · simp [bankOrdinaryCoreSources_of_le_five hp5]
  · have hp6 : 6 ≤ p := by omega
    have hpPower : ¬ IsPowerOfTwo p :=
      prime_not_isPowerOfTwo_of_five_le hp (by omega)
    have hsubset : bankOrdinaryCoreSources p ⊆ Finset.Icc 1 p := by
      intro source hsource
      have hspec := bankOrdinaryCoreSource_spec
        (show 5 ≤ p by omega) hpPower hsource
      exact Finset.mem_Icc.mpr
        ⟨(show 1 ≤ 6 by norm_num).trans hspec.1,
          bankOrdinaryCoreSource_le_start hsource⟩
    exact (Finset.card_le_card hsubset).trans (by simp)

/-- The number of signed beta slots is exactly twice the common one-sided
bottom demand. -/
theorem bankOrdinarySignedSlots_card_eq_two_mul_demand (n : ℕ) :
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

/-- The complete ordinary request family has the pointwise coarse bound
`2*yNat*sum beta`.  In particular, the source multiplicity contributes only
one additional factor of `yNat`. -/
theorem bankOrdinaryPaperRequests_card_le_two_mul_yNat_mul_demand
    (n : ℕ) :
    (bankOrdinaryPaperRequests n).card ≤
      2 * yNat n * bankBottomPaperDemand n := by
  rw [bankOrdinaryPaperRequests, Finset.card_univ, Fintype.card_sigma]
  calc
    (∑ slot : SignedBankSlot (bankRoundingBetaOnSupport n),
        Fintype.card ↑(bankOrdinaryCoreSources slot.1.1)) ≤
        ∑ _slot : SignedBankSlot (bankRoundingBetaOnSupport n),
          yNat n := by
            apply Finset.sum_le_sum
            intro slot _hslot
            simpa only [Fintype.card_coe] using
              (bankOrdinaryPrimeCoreSources_card_le
                  (bankRoundingPrimeSupport_prime slot.1.property)).trans
                (bankRoundingPrimeSupport_le_yNat slot.1.property)
    _ = Fintype.card
          (SignedBankSlot (bankRoundingBetaOnSupport n)) * yNat n := by
            simp
    _ = 2 * yNat n * bankBottomPaperDemand n := by
      rw [bankOrdinarySignedSlots_card_eq_two_mul_demand]
      ring

/-- Globally there are only `O(yNat²)` ordinary components.  This is the
coarse estimate needed to replace the cofactor of every ordinary marker,
without singling out a collision prefix. -/
theorem bankOrdinaryPaperRequests_card_isBigO_yNat_sq :
    (fun n : ℕ ↦ ((bankOrdinaryPaperRequests n).card : ℝ))
      =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
  have hpoint :
      (fun n : ℕ ↦ ((bankOrdinaryPaperRequests n).card : ℝ))
        =O[atTop]
          (fun n : ℕ ↦
            2 * (yNat n : ℝ) * bankBottomPaperDemand n) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (bankOrdinaryPaperRequests n).card),
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ 2 * (yNat n : ℝ) * bankBottomPaperDemand n),
      one_mul]
    exact_mod_cast
      bankOrdinaryPaperRequests_card_le_two_mul_yNat_mul_demand n
  have hproduct :=
    (isBigO_refl (fun n : ℕ ↦ (yNat n : ℝ)) atTop).mul
      bankBottomPaperDemand_isBigO_yNat
  have hscaled := hproduct.const_mul_left (2 : ℝ)
  exact hpoint.trans (hscaled.congr'
    (Eventually.of_forall fun n ↦ by ring)
    (Eventually.of_forall fun n ↦ (pow_two (yNat n : ℝ)).symm))

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



































private theorem stateValues_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.sourceStateValue request ∈ factorInterval n M ∧
      R.targetStateValue request ∈ factorInterval n M := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  let P := R.marker request
  let q := bankOrdinaryPaperRequestSource request.1
  let b := bankOrdinaryPaperRequestTarget request.1
  let Q := bankOrdinaryScale
    (bankOrdinaryPaperRequestPool n request.1).1
  have hPpos : (0 : ℚ) < P := by
    exact_mod_cast (R.marker_prime request).pos
  have hPnonneg : (0 : ℚ) ≤ P := hPpos.le
  have hmarker := heligible.2.2.2.1
  have hcell := hspec.2.2.2.2.2.2
  change 4 * (n : ℚ) < 3 * Q * P ∧
    2 * Q * P ≤ 3 * (n : ℚ) at hmarker
  change (Q < (q : ℚ) ∧ (q : ℚ) ≤ 4 * Q / 3) ∧
    3 * Q / 4 < (b : ℚ) at hcell
  have hQq := mul_lt_mul_of_pos_left hcell.1.1
    hPpos
  have hqUpper := mul_le_mul_of_nonneg_left hcell.1.2 hPnonneg
  have hbLower := mul_lt_mul_of_pos_left hcell.2
    hPpos
  have hmarkerLower := hmarker.1
  have hmarkerUpper := hmarker.2
  have hsourceLowerQ : (n : ℚ) < P * q := by
    nlinarith [hmarkerLower, hQq]
  have htargetLowerQ : (n : ℚ) < P * b := by
    nlinarith [hmarkerLower, hbLower]
  have hcellSourceUpper : P * (4 * Q / 3) ≤ 2 * (n : ℚ) := by
    have hscaled := mul_le_mul_of_nonneg_left hmarkerUpper
      (by norm_num : (0 : ℚ) ≤ 2 / 3)
    convert hscaled using 1 <;> ring
  have hsourceUpperQ : P * q ≤ 2 * (n : ℚ) := by
    exact hqUpper.trans hcellSourceUpper
  have hsourceLower : n < P * q := by exact_mod_cast hsourceLowerQ
  have htargetLower : n < P * b := by exact_mod_cast htargetLowerQ
  have hsourceUpper : P * q ≤ M := by
    have : P * q ≤ 2 * n := by exact_mod_cast hsourceUpperQ
    exact this.trans R.two_mul_n_le_M
  have htargetUpper : P * b ≤ M := by
    have hbq : b ≤ q := hspec.2.2.2.2.1.le
    exact (Nat.mul_le_mul_left P hbq).trans hsourceUpper
  simp only [sourceStateValue, targetStateValue, factorInterval,
    Finset.mem_Ioc]
  exact ⟨⟨hsourceLower, hsourceUpper⟩,
    ⟨htargetLower, htargetUpper⟩⟩

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

















/-- Marker injectivity makes the marker set equinumerous with the complete
ordinary component-request family. -/
theorem markers_card_eq_paperRequests_card
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M) :
    R.markers.card = (bankOrdinaryPaperRequests n).card := by
  rw [markers, Finset.card_image_of_injective _ R.marker_injective]
  simp



















/-! ## The three actual occurrences and global collision-freedom -/





theorem two_mul_n_lt_donorValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    2 * n < R.donorValue request :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.2.2.2.2.2.1



























theorem componentOccurrence_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ R.componentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  rw [componentOccurrences, Finset.mem_image] at hoccurrence
  obtain ⟨kind, _hkind, hvalue⟩ := hoccurrence
  cases kind
  · simpa only [← hvalue, occurrenceValue_sourceState] using
      (R.stateValues_mem_factorInterval request).1
  · simpa only [← hvalue, occurrenceValue_targetState] using
      (R.stateValues_mem_factorInterval request).2
  · simpa only [← hvalue, occurrenceValue_donor] using
      R.donorValue_mem_factorInterval request





/-! ## Realized component and signed-slot changes -/























end BankOrdinaryPaperRealization

/-! ## Eventual realized allocation -/

/-- Terminal realization compatible with the bottom realization object: at
the paper endpoint, every ordinary request has actual factor occurrences and
all request occurrence sets are pairwise disjoint. -/
theorem eventually_exists_bankOrdinaryPaperRealization
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty (BankOrdinaryPaperRealization n
        (upperEndpoint n (upperTailLength c n))) := by
  filter_upwards [eventually_exists_bankOrdinaryPaper_injective_assignment hc,
      eventually_ge_atTop 1] with n hmatching hn
  obtain ⟨matching, _hinjective, _heligible⟩ := hmatching
  exact ⟨⟨matching, hn,
    two_mul_le_upperEndpoint n (upperTailLength c n)⟩⟩

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













theorem ordinaryMarkers_disjoint_bottomMarkers
    {n M : ℕ} (R : BankPaperRealization n M) :
    Disjoint R.ordinaryMarkers R.bottomMarkers := by
  rw [Finset.disjoint_left]
  intro P hordinary hbottom
  rw [ordinaryMarkers, BankOrdinaryPaperRealization.markers,
    Finset.mem_image] at hordinary
  obtain ⟨ordinaryRequest, _hrequest, hordinaryP⟩ := hordinary
  rw [bottomMarkers, BankBottomPaperRealization.relevantMarkers,
    Finset.mem_image] at hbottom
  obtain ⟨bottomRequest, _hrequest, hbottomP⟩ := hbottom
  have hlt := R.ordinaryMarker_lt_bottomMarker ordinaryRequest
    (bankBottomRelevantRequestToPaperRequest bottomRequest)
  omega

theorem allMarkers_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.allMarkers.card =
      (bankOrdinaryPaperRequests n).card +
        (bankBottomRelevantPaperRequests n).card := by
  rw [allMarkers,
    Finset.card_union_of_disjoint R.ordinaryMarkers_disjoint_bottomMarkers,
    ordinaryMarkers, bottomMarkers,
    R.ordinary.markers_card_eq_paperRequests_card,
    R.bottom.card_relevantMarkers]

/-! ## Cross-family actual occurrence disjointness -/

















end BankPaperRealization

/-! ## Terminal combined realization -/

theorem eventually_exists_bankPaperRealization
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty (BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) := by
  filter_upwards [eventually_exists_bankBottomPaper_component_realization hc,
      eventually_exists_bankOrdinaryPaperRealization hc,
      eventually_bankBottom_six_le_yNat,
      eventually_bankBottom_three_mul_yNat_le_self]
      with n hbottom hordinary hySix hgeometry
  obtain ⟨bottom, _hinterval, _hsignature, _hdisjoint,
    _hmarkerCard, _hmarkerBound, _hoccurrenceBound⟩ := hbottom
  exact ⟨⟨bottom, Classical.choice hordinary, hySix, hgeometry⟩⟩

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

/-- Routing at the literal cutoff lands in row zero or a positive row no
larger than the fixed prefix depth. -/
theorem largeCentralPrime_rowZero_or_fixedPrefix
    {R n p : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n)
    (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      ((n < p ∧ p ≤ 2 * n) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r) := by
  have hnPos : 0 < n :=
    (centralAnchorCutoffThreshold_pos R).trans_le hn
  have hroute := largeCentralPrime_rowZero_or_stationary hnPos
    (two_mul_lt_centralAnchorCutoff_sq hn) hp
  refine ⟨hroute.1, ?_⟩
  rcases hroute.2 with hzero | ⟨r, hrPos, hr, hpRow⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨r, hrPos, by
      rw [hr]
      exact largeCentralPrime_div_le_fixedPrefix hp, hr, hpRow⟩























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorModificationAlgebra -/
section


/-!
# Valuation cost of finite central-cofactor modifications

Later bank guards change the routed cofactor at a finite, explicit set of
central marker primes.  This file records the exact valuation cost of that
operation.  It does not assume that a modification is available: both
cofactor choices, the changed marker set, and equality off that set are
literal inputs.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- A positive integer at most `B` has no more than `log_ℓ B` copies of a
prime `ℓ` in its factorization. -/
theorem factorization_le_log_of_pos_le
    {a B ℓ : ℕ} (ha : 0 < a) (haB : a ≤ B) (hℓ : ℓ.Prime) :
    a.factorization ℓ ≤ Nat.log ℓ B := by
  have hpowDvd : ℓ ^ (a.factorization ℓ) ∣ a :=
    (hℓ.pow_dvd_iff_le_factorization ha.ne').mpr le_rfl
  have hpowLe : ℓ ^ (a.factorization ℓ) ≤ a :=
    Nat.le_of_dvd ha hpowDvd
  exact (Nat.le_log_of_pow_le hℓ.one_lt hpowLe).trans
    (Nat.log_mono_right haB)





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperAnchorGuards -/
section


/-!
# Actual bank markers as central-anchor guards

This is the finite composition layer between the realized bank components
and the guarded central-cofactor construction.  The set of changed markers
is literally the intersection of the realized bank marker set with the
large-central-prime set.  Its two forbidden cores are recovered from the
unique incident component.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

namespace BankPaperRealization









theorem centralChangedMarkers_subset_largeCentralPrimes
    {n M : ℕ} (R : BankPaperRealization n M) (depth : ℕ) :
    R.centralChangedMarkers depth ⊆
      largeCentralPrimes n (centralAnchorCutoff depth n) := by
  exact Finset.inter_subset_right

theorem centralChangedMarkers_subset_allMarkers
    {n M : ℕ} (R : BankPaperRealization n M) (depth : ℕ) :
    R.centralChangedMarkers depth ⊆ R.allMarkers := by
  exact Finset.inter_subset_left

theorem centralChangedMarkers_card_le
    {n M : ℕ} (R : BankPaperRealization n M) (depth : ℕ) :
    (R.centralChangedMarkers depth).card ≤
      (bankOrdinaryPaperRequests n).card +
        8 * bankBottomPaperDemand n := by
  calc
    (R.centralChangedMarkers depth).card ≤ R.allMarkers.card :=
      Finset.card_le_card (R.centralChangedMarkers_subset_allMarkers depth)
    _ = (bankOrdinaryPaperRequests n).card +
        (bankBottomRelevantPaperRequests n).card := R.allMarkers_card
    _ ≤ (bankOrdinaryPaperRequests n).card +
        8 * bankBottomPaperDemand n := by
      exact Nat.add_le_add_left
        (by
          rw [← R.bottom.card_relevantMarkers]
          exact R.bottom.card_relevantMarkers_le_demand)
        _

/-- Membership in the ordinary marker set unfolds the canonical incident
cores to the actual request source and target. -/
theorem anchorGuardIncidentCores_of_ordinary
    {n M : ℕ} (R : BankPaperRealization n M)
    (P : ↑R.ordinary.markers) :
    R.anchorGuardIncidentCores P.1 =
      (bankOrdinaryPaperRequestSource (R.ordinary.requestForMarker P).1,
        bankOrdinaryPaperRequestTarget (R.ordinary.requestForMarker P).1) := by
  simp [anchorGuardIncidentCores, P.property]

/-- Membership in the bottom marker set unfolds to the unique relevant
bottom request's two actual state cores. -/
theorem anchorGuardIncidentCores_of_bottom
    {n M : ℕ} (R : BankPaperRealization n M)
    (P : ↑R.bottom.relevantMarkers) :
    R.anchorGuardIncidentCores P.1 =
      R.bottom.relevantMarkerIncidentStateCores P := by
  have hnotOrdinary : P.1 ∉ R.ordinary.markers := by
    intro hpOrdinary
    exact (Finset.disjoint_left.mp
      R.ordinaryMarkers_disjoint_bottomMarkers) hpOrdinary P.property
  simp [anchorGuardIncidentCores, hnotOrdinary, P.property]

/-- Every changed marker lies below `n`.  This is immediate for ordinary
markers from `3P<n`; for every bottom row it follows from `M≤3n` and the
literal upper endpoint of that row. -/
theorem centralChangedMarker_le_n
    {n M depth : ℕ} (R : BankPaperRealization n M)
    (hM : M ≤ 3 * n) :
    ∀ p ∈ R.centralChangedMarkers depth, p ≤ n := by
  intro p hpChanged
  have hpAll := R.centralChangedMarkers_subset_allMarkers depth hpChanged
  rw [allMarkers, ordinaryMarkers, bottomMarkers,
    Finset.mem_union] at hpAll
  rcases hpAll with hpOrdinary | hpBottom
  · let P : ↑R.ordinary.markers := ⟨p, hpOrdinary⟩
    have hsmall := R.ordinary.three_mul_marker_lt_n
      (R.ordinary.requestForMarker P)
    have hmarker :
        R.ordinary.marker (R.ordinary.requestForMarker P) = p := by
      simpa only [P] using R.ordinary.marker_requestForMarker P
    rw [hmarker] at hsmall
    omega
  · let P : ↑R.bottom.relevantMarkers := ⟨p, hpBottom⟩
    let request := bankBottomRelevantRequestToPaperRequest
      (R.bottom.requestForRelevantMarker P)
    have hbound := R.bottom.marker_le_n
      R.ordinary.two_mul_n_le_M hM request
    have hmarker : R.bottom.marker request = p := by
      exact R.bottom.marker_requestForRelevantMarker P
    simpa only [hmarker] using hbound

/-- Eventually the paper endpoint is already below `5n/2`.  This slightly
sharper elementary endpoint bound is used only to identify the unique
row-one bottom move. -/
theorem eventually_two_mul_upperEndpoint_le_five_mul
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      2 * upperEndpoint n (upperTailLength c n) ≤ 5 * n := by
  have hsmall := (upperTailLength_ratio_tendsto_zero hc).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn htail
  have hnPos : (0 : ℝ) < n := by exact_mod_cast htail
  have hcast : (2 * upperTailLength c n : ℕ) ≤ n := by
    have hreal : (2 : ℝ) * upperTailLength c n < n := by
      have := (div_lt_iff₀ hnPos).mp hn
      nlinarith
    exact_mod_cast hreal.le
  simp only [upperEndpoint]
  omega

/-- At a changed row-one marker, neither actual incident state core is `3`.
For ordinary components both cores are at least five.  Among the four bottom
rows, the literal marker intervals and central stationary-row inequalities
leave only `2→1`, whose cores are `(2,4)`. -/
theorem centralChangedMarker_rowOne_avoids_three
    {n M depth : ℕ} (R : BankPaperRealization n M)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hMThree : M ≤ 3 * n) (hMFive : 2 * M ≤ 5 * n) :
    ∀ p ∈ R.centralChangedMarkers depth, n / p = 1 →
      3 ≠ R.anchorGuardLeftCore p ∧
        3 ≠ R.anchorGuardRightCore p := by
  intro p hpChanged hrowOne
  have hpAll := R.centralChangedMarkers_subset_allMarkers depth hpChanged
  have hpLarge := R.centralChangedMarkers_subset_largeCentralPrimes depth hpChanged
  rw [allMarkers, ordinaryMarkers, bottomMarkers,
    Finset.mem_union] at hpAll
  rcases hpAll with hpOrdinary | hpBottom
  · let P : ↑R.ordinary.markers := ⟨p, hpOrdinary⟩
    have hspec := bankOrdinaryPaperRequest_component_spec
      (R.ordinary.requestForMarker P).1
    have hsourceSix := hspec.1
    have htargetFive := hspec.2.2.2.1
    have hcores :
        R.anchorGuardIncidentCores p =
          (bankOrdinaryPaperRequestSource
              (R.ordinary.requestForMarker P).1,
            bankOrdinaryPaperRequestTarget
              (R.ordinary.requestForMarker P).1) := by
      simpa only [P] using R.anchorGuardIncidentCores_of_ordinary P
    simp only [anchorGuardLeftCore, anchorGuardRightCore, hcores]
    constructor <;> omega
  · let P : ↑R.bottom.relevantMarkers := ⟨p, hpBottom⟩
    let relevantRequest := R.bottom.requestForRelevantMarker P
    let request := bankBottomRelevantRequestToPaperRequest relevantRequest
    have hmarker : R.bottom.marker request = p := by
      exact R.bottom.marker_requestForRelevantMarker P
    have hpRoute :=
      (largeCentralPrime_rowZero_or_fixedPrefix hnCutoff hpLarge).2
    have hpLe : p ≤ n :=
      R.centralChangedMarker_le_n hMThree p hpChanged
    have hpStationary : p ∈ stationaryPrimeLayer n 1 := by
      rcases hpRoute with hzero |
          ⟨r, _hrPos, _hrDepth, hrEq, hpStationary⟩
      · exact (not_lt_of_ge hpLe hzero.1).elim
      · have hrOne : r = 1 := by omega
        simpa only [hrOne] using hpStationary
    have hpStationaryData := mem_stationaryPrimeLayer.mp hpStationary
    have hmarkerRow := R.bottom.marker_mem_row
      R.ordinary.two_mul_n_le_M request
    rw [hmarker] at hmarkerRow
    have hmove : R.bottom.move request = .twoToOne := by
      cases hmoveCases : R.bottom.move request
      · have hupper := (Finset.mem_Ioc.mp hmarkerRow).2
        simp only [hmoveCases,
          bankBottomMarkerUpper] at hupper
        exfalso
        omega
      · have hupper := (Finset.mem_Ioc.mp hmarkerRow).2
        simp only [hmoveCases,
          bankBottomMarkerUpper] at hupper
        exfalso
        omega
      · have hlower := (Finset.mem_Ioc.mp hmarkerRow).1
        simp only [hmoveCases,
          bankBottomMarkerLower] at hlower
        have htwoNltRaw :=
          (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).mp hlower
        have htwoNlt : 2 * n < 3 * p := by
          omega
        exfalso
        omega
      · rfl
    have hcoresBottom := R.anchorGuardIncidentCores_of_bottom P
    have hcanonicalCores :
        R.bottom.relevantMarkerIncidentStateCores P = (2, 4) := by
      change bankBottomIncidentStateCores
        (R.bottom.move request) = (2, 4)
      rw [hmove]
      rfl
    rw [anchorGuardLeftCore, anchorGuardRightCore,
      hcoresBottom, hcanonicalCores]
    norm_num

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperAnchorChangeBudget -/
section


/-!
# The cost of guarding every realized bank marker is negligible

The deliberately coarse global marker bound is `O(yNat²)`.  Since
`yNat² = o(n/log n)`, even changing every realized bank marker which meets
the fixed central prefix consumes only an arbitrarily small fixed fraction
of the central valuation reserve.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section



theorem bankPaperAnchorMarkerBudget_isBigO_yNat_sq :
    (fun n : ℕ ↦ (bankPaperAnchorMarkerBudget n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
  have hySq :
      (fun n : ℕ ↦ (yNat n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_bankBottom_six_le_yNat] with n hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ yNat n),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (yNat n : ℝ)), one_mul]
    have hyOne : (1 : ℝ) ≤ yNat n := by exact_mod_cast (show 1 ≤ yNat n by omega)
    nlinarith [sq_nonneg ((yNat n : ℝ) - 1)]
  have hdemandSq := bankBottomPaperDemand_isBigO_yNat.trans hySq
  have hsum := bankOrdinaryPaperRequests_card_isBigO_yNat_sq.add
    (hdemandSq.const_mul_left (8 : ℝ))
  apply hsum.congr'
  · exact Eventually.of_forall fun n ↦ by
      simp only [bankPaperAnchorMarkerBudget, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat]
  · exact Eventually.of_forall fun _n ↦ rfl

/-- The coarse all-marker budget itself is little-o of the central scale. -/
theorem bankPaperAnchorMarkerBudget_isLittleO_secondOrderScale :
    (fun n : ℕ ↦ (bankPaperAnchorMarkerBudget n : ℝ)) =o[atTop]
      secondOrderScale := by
  have hyLittle :
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) =o[atTop]
        secondOrderScale := by
    apply (isLittleO_iff_tendsto' ?_).mpr
      yNat_sq_div_secondOrderScale_tendsto_zero
    filter_upwards [eventually_secondOrderScale_pos] with n hscale hzero
    exact (hscale.ne' hzero).elim
  exact bankPaperAnchorMarkerBudget_isBigO_yNat_sq.trans_isLittleO hyLittle

/-- Multiplying by the fixed worst-case cofactor valuation still gives a
vanishing normalized change cost. -/
theorem bankPaperAnchorChangeCost_normalized_tendsto_zero (depth : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        ((bankPaperAnchorMarkerBudget n * Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  have hscaled :=
    bankPaperAnchorMarkerBudget_isLittleO_secondOrderScale.const_mul_left
      ((Nat.log 2 (2 * depth + 1) : ℕ) : ℝ)
  have hlimit := hscaled.tendsto_div_nhds_zero
  apply hlimit.congr'
  exact Eventually.of_forall fun n ↦ by
    push_cast
    ring

/-- Uniformly over every realization and endpoint, the literal changed-set
cost is eventually below any prescribed positive multiple of the central
scale. -/
theorem eventually_bankPaper_centralChangedMarkers_changeCost_le
    (depth : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ) (R : BankPaperRealization n M),
      (((R.centralChangedMarkers depth).card *
          Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) ≤
        delta * secondOrderScale n := by
  have hsmall := (bankPaperAnchorChangeCost_normalized_tendsto_zero depth).eventually
    (eventually_lt_nhds hdelta)
  filter_upwards [hsmall, eventually_secondOrderScale_pos] with n hn hscale
  have hbudget :
      ((bankPaperAnchorMarkerBudget n * Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) ≤
        delta * secondOrderScale n := by
    have hratio := (div_lt_iff₀ hscale).mp hn
    exact hratio.le
  intro M R
  have hcard : (R.centralChangedMarkers depth).card ≤
      bankPaperAnchorMarkerBudget n := by
    simpa only [bankPaperAnchorMarkerBudget] using
      R.centralChangedMarkers_card_le depth
  have hcostNat :
      (R.centralChangedMarkers depth).card * Nat.log 2 (2 * depth + 1) ≤
        bankPaperAnchorMarkerBudget n * Nat.log 2 (2 * depth + 1) :=
    Nat.mul_le_mul_right _ hcard
  exact (by exact_mod_cast hcostNat :
      (((R.centralChangedMarkers depth).card *
        Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) ≤
      ((bankPaperAnchorMarkerBudget n *
        Nat.log 2 (2 * depth + 1) : ℕ) : ℝ)).trans hbudget

/-- Prime-by-prime form matching the guarded central certificate.  The
finite support is handled uniformly using its largest possible denominator.
-/
theorem eventually_bankPaper_changeCost_le_sixth_reserve
    {c : ℝ} (hc : C0 < c) {depth : ℕ} (hdepth : 1 ≤ depth) :
    ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ) (R : BankPaperRealization n M),
      ∀ ℓ ∈ primesUpTo (2 * depth + 1),
        (((R.centralChangedMarkers depth).card *
            Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) ≤
          (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n := by
  let delta : ℝ :=
    (c - C0) / (6 * (((2 * depth + 1 - 1 : ℕ) : ℝ)))
  have hepsilon : 0 < c - C0 := sub_pos.mpr hc
  have hlargest : 0 < (((2 * depth + 1 - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < 2 * depth + 1 - 1 by omega)
  have hdelta : 0 < delta := by
    exact div_pos hepsilon (mul_pos (by norm_num) hlargest)
  have hbase :=
    eventually_bankPaper_centralChangedMarkers_changeCost_le depth hdelta
  filter_upwards [hbase, eventually_secondOrderScale_pos] with n hn hscale
  intro M R ℓ hℓ
  have hℓPrime := (mem_primesUpTo.mp hℓ).1
  have hℓBound := (mem_primesUpTo.mp hℓ).2
  have hsmall : 0 < (((ℓ - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_of_lt hℓPrime.one_lt
  have hdenLe : (((ℓ - 1 : ℕ) : ℝ)) ≤
      (((2 * depth + 1 - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show ℓ - 1 ≤ 2 * depth + 1 - 1 by omega)
  have hcoefficient : delta ≤
      (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) := by
    dsimp [delta]
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hlargest)
      (mul_pos (by norm_num) hsmall)).2
    nlinarith
  exact (hn M R).trans
    (mul_le_mul_of_nonneg_right hcoefficient hscale.le)

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

















/-- Every named occurrence of every component lies in the factor interval. -/
theorem prechargeComponentOccurrence_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) {occurrence : ℕ}
    (hoccurrence : occurrence ∈
      R.prechargeComponentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  cases request with
  | inl request =>
      exact R.bottom.componentOccurrence_mem_factorInterval
        R.ordinary.two_mul_n_le_M
        (bankBottomRelevantRequestToPaperRequest request) hoccurrence
  | inr request =>
      exact R.ordinary.componentOccurrence_mem_factorInterval
        request hoccurrence

theorem prechargeBaseStateValue_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ∈ factorInterval n M :=
  R.prechargeComponentOccurrence_mem_factorInterval request
    (R.prechargeBaseStateValue_mem_componentOccurrences request)



theorem prechargeDonorValue_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ factorInterval n M :=
  R.prechargeComponentOccurrence_mem_factorInterval request
    (R.prechargeDonorValue_mem_componentOccurrences request)

/-! ## Complete rough signatures -/





/-- Above the rough cutoff, a component's base token and its actual donor
have exactly the same prime exponent. -/
theorem prechargeBase_donor_factorization_eq_of_yNat_lt
    {n M p : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) (hp : yNat n < p) :
    (R.prechargeBaseStateValue request).factorization p =
      (R.prechargeDonorValue request).factorization p := by
  have hcoordinate := congrArg (fun signature : ℕ →₀ ℕ ↦ signature p)
    (R.prechargeBase_donor_completeRoughSignature_eq request)
  simpa only [completeRoughSignature_apply, if_pos hp] using hcoordinate

/-! ## Endpoint and donor injectivity -/





















/-! ## Literal finite states, donor tail, and replacement map -/













theorem prechargeBaseState_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseState.card =
      Fintype.card (BankPaperMarkerRequest n) := by
  rw [prechargeBaseState, indexedPathState,
    Finset.card_image_of_injective _ R.prechargeBaseStateValue_injective]
  simp







theorem prechargeBaseState_subset_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseState ⊆ factorInterval n M := by
  intro value hvalue
  rw [prechargeBaseState, indexedPathState, Finset.mem_image] at hvalue
  obtain ⟨request, _hrequest, rfl⟩ := hvalue
  exact R.prechargeBaseStateValue_mem_factorInterval request



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

/-- At the literal endpoint `upperEndpoint n h`, the product of all actual
bank donors divides the central tail product. -/
theorem prechargeDonorSet_prod_dvd_centralTailProduct
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    R.prechargeDonorSet.prod id ∣ centralTailProduct n h := by
  change R.prechargeDonorSet.prod id ∣
    (Finset.Ioc (2 * n) (upperEndpoint n h)).prod id
  exact Finset.prod_dvd_prod_of_subset
    R.prechargeDonorSet (Finset.Ioc (2 * n) (upperEndpoint n h)) id
      R.prechargeDonorSet_subset_tail



















/-! ## Component counts and the base product -/



theorem card_bankPaperMarkerRequest (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) =
      (bankBottomRelevantPaperRequests n).card +
        (bankOrdinaryPaperRequests n).card := by
  change Fintype.card
      (↑(bankBottomRelevantPaperRequests n) ⊕
        ↑(bankOrdinaryPaperRequests n)) = _
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]

/-- The global component index has a realization-independent coarse bound.
The bottom contribution is a filtered subfamily of the full eight-row
request rectangle. -/
theorem card_bankPaperMarkerRequest_le_anchorMarkerBudget (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperAnchorMarkerBudget n := by
  rw [card_bankPaperMarkerRequest, bankPaperAnchorMarkerBudget]
  have hbottom : (bankBottomRelevantPaperRequests n).card ≤
      8 * bankBottomPaperDemand n := by
    calc
      (bankBottomRelevantPaperRequests n).card ≤
          (bankBottomPaperRequests n).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 8 * bankBottomPaperDemand n :=
        card_bankBottomPaperRequests n
  omega

theorem prechargeComponentCount_le_anchorMarkerBudget
    {n M : ℕ} (_R : BankPaperRealization n M) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperAnchorMarkerBudget n := by
  exact card_bankPaperMarkerRequest_le_anchorMarkerBudget n



/-- Exact product after forgetting the injective component labels. -/
theorem prechargeBaseStateProduct_eq_componentProduct
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseStateProduct =
      ∏ request : BankPaperMarkerRequest n,
        R.prechargeBaseStateValue request := by
  rw [prechargeBaseStateProduct, prechargeBaseState, indexedPathState,
    Finset.prod_image (R.prechargeBaseStateValue_injective).injOn]
  simp

/-- Exact donor-set product after forgetting its injective component
labels. -/
theorem prechargeDonorSet_prod_eq_componentProduct
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet.prod id =
      ∏ request : BankPaperMarkerRequest n,
        R.prechargeDonorValue request := by
  rw [prechargeDonorSet, indexedPathState,
    Finset.prod_image (R.prechargeDonorValue_injective).injOn]
  simp

/-- Replacing every actual donor by its base token preserves the valuation
of the full product at every prime above the rough cutoff. -/
theorem prechargeBaseStateProduct_factorization_eq_donorSet_prod
    {n M p : ℕ} (R : BankPaperRealization n M)
    (hp : yNat n < p) :
    (R.prechargeBaseStateProduct).factorization p =
      (R.prechargeDonorSet.prod id).factorization p := by
  have hbaseNe : ∀ request : BankPaperMarkerRequest n,
      R.prechargeBaseStateValue request ≠ 0 := by
    intro request
    have hinterval := R.prechargeBaseStateValue_mem_factorInterval request
    have hdata : n < R.prechargeBaseStateValue request ∧
        R.prechargeBaseStateValue request ≤ M := by
      simpa only [factorInterval, Finset.mem_Ioc] using hinterval
    omega
  have hdonorNe : ∀ request : BankPaperMarkerRequest n,
      R.prechargeDonorValue request ≠ 0 := by
    intro request
    have hinterval := R.prechargeDonorValue_mem_factorInterval request
    have hdata : n < R.prechargeDonorValue request ∧
        R.prechargeDonorValue request ≤ M := by
      simpa only [factorInterval, Finset.mem_Ioc] using hinterval
    omega
  have hbaseFactorization :
      (∏ request : BankPaperMarkerRequest n,
          R.prechargeBaseStateValue request).factorization p =
        ∑ request : BankPaperMarkerRequest n,
          (R.prechargeBaseStateValue request).factorization p :=
    Nat.factorization_prod_apply
      (fun request _hrequest ↦ hbaseNe request)
  have hdonorFactorization :
      (∏ request : BankPaperMarkerRequest n,
          R.prechargeDonorValue request).factorization p =
        ∑ request : BankPaperMarkerRequest n,
          (R.prechargeDonorValue request).factorization p :=
    Nat.factorization_prod_apply
      (fun request _hrequest ↦ hdonorNe request)
  rw [R.prechargeBaseStateProduct_eq_componentProduct,
    R.prechargeDonorSet_prod_eq_componentProduct,
    hbaseFactorization, hdonorFactorization]
  apply Finset.sum_congr rfl
  intro request _hrequest
  exact R.prechargeBase_donor_factorization_eq_of_yNat_lt request hp



/-- Uniform prime-by-prime valuation bound for the complete precharged base
product.  It is stated for every prime, hence in particular for every small
prime used by the central reserve. -/
theorem prechargeBaseStateProduct_factorization_le
    {n M ℓ : ℕ} (R : BankPaperRealization n M) (hℓ : ℓ.Prime) :
    (R.prechargeBaseStateProduct).factorization ℓ ≤
      Fintype.card (BankPaperMarkerRequest n) * Nat.log 2 M := by
  rw [prechargeBaseStateProduct, Nat.factorization_prod_apply]
  · calc
      (∑ value ∈ R.prechargeBaseState, value.factorization ℓ) ≤
          ∑ _value ∈ R.prechargeBaseState, Nat.log 2 M := by
        apply Finset.sum_le_sum
        intro value hvalue
        have hinterval := R.prechargeBaseState_subset_factorInterval hvalue
        have hintervalData : n < value ∧ value ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using hinterval
        have hvaluePos : 0 < value := by omega
        have hvalueLe : value ≤ M := hintervalData.2
        exact (factorization_le_log_of_pos_le
          hvaluePos hvalueLe hℓ).trans
            (Nat.log_anti_left Nat.one_lt_two hℓ.two_le)
      _ = R.prechargeBaseState.card * Nat.log 2 M := by simp
      _ = Fintype.card (BankPaperMarkerRequest n) * Nat.log 2 M := by
        rw [R.prechargeBaseState_card]
  · intro value hvalue
    have hinterval := R.prechargeBaseState_subset_factorInterval hvalue
    have hintervalData : n < value ∧ value ≤ M := by
      simpa only [factorInterval, Finset.mem_Ioc] using hinterval
    have hvaluePos : 0 < value :=
      lt_of_le_of_lt (Nat.zero_le n) hintervalData.1
    simpa only [id_eq] using hvaluePos.ne'

theorem prechargeBaseStateProduct_factorization_le_anchorMarkerBudget
    {n M ℓ : ℕ} (R : BankPaperRealization n M) (hℓ : ℓ.Prime) :
    (R.prechargeBaseStateProduct).factorization ℓ ≤
      bankPaperAnchorMarkerBudget n * Nat.log 2 M := by
  exact (R.prechargeBaseStateProduct_factorization_le hℓ).trans
    (Nat.mul_le_mul_right _ R.prechargeComponentCount_le_anchorMarkerBudget)

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargeDivisibilityAlgebra -/
section


/-!
# Divisibility algebra for the precharged bank

The guarded central divisor has fixed prime support.  Above the moving rough
cutoff, the precharged base product has exactly the donor-product valuations,
and that donor product is a literal subset-product of the factorial tail.
Consequently the only remaining capacity obligation is the displayed finite
range of primes up to `yNat n`.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Coordinatewise divisibility with one cutoff.  The first factor vanishes
above the cutoff; below it the two valuation demands are charged together. -/
theorem mul_dvd_of_factorization_split
    {D B T cutoff : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hT : 0 < T)
    (hDhigh : ∀ p, p.Prime → cutoff < p → D.factorization p = 0)
    (hlow : ∀ p, p.Prime → p ≤ cutoff →
      D.factorization p + B.factorization p ≤ T.factorization p)
    (hhigh : ∀ p, p.Prime → cutoff < p →
      B.factorization p ≤ T.factorization p) :
    D * B ∣ T := by
  rw [← Nat.factorization_le_iff_dvd
    (mul_ne_zero hD.ne' hB.ne') hT.ne']
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul hD.ne' hB.ne', Finsupp.add_apply]
    by_cases hpCutoff : p ≤ cutoff
    · exact hlow p hp hpCutoff
    · rw [hDhigh p hp (Nat.lt_of_not_ge hpCutoff), zero_add]
      exact hhigh p hp (Nat.lt_of_not_ge hpCutoff)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-- High coordinates may be discharged by comparison with a positive donor
product which already divides the target. -/
theorem mul_dvd_of_factorization_split_with_donor
    {D B donor T cutoff : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hdonor : 0 < donor) (hT : 0 < T)
    (hdonorDvd : donor ∣ T)
    (hDhigh : ∀ p, p.Prime → cutoff < p → D.factorization p = 0)
    (hbaseDonor : ∀ p, p.Prime → cutoff < p →
      B.factorization p = donor.factorization p)
    (hlow : ∀ p, p.Prime → p ≤ cutoff →
      D.factorization p + B.factorization p ≤ T.factorization p) :
    D * B ∣ T := by
  apply mul_dvd_of_factorization_split hD hB hT hDhigh hlow
  intro p hp hpCutoff
  rw [hbaseDonor p hp hpCutoff]
  exact (Nat.factorization_le_iff_dvd hdonor.ne' hT.ne').mpr
    hdonorDvd p

namespace GuardedCentralAnchorCertificate

/-- The exact paper specialization.  Once low-prime capacity is supplied,
the guarded anchor divisor times the actual precharge product divides the
literal upper-tail product. -/
theorem mul_prechargeBaseStateProduct_dvd_centralTailProduct
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hsupportCutoff : 2 * depth + 1 ≤ yNat n)
    (hlow : ∀ p, p.Prime → p ≤ yNat n →
      (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q).factorization p +
        (R.prechargeBaseStateProduct).factorization p ≤
      (centralTailProduct n
        (upperTailLength c n)).factorization p) :
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
        R.prechargeBaseStateProduct ∣
      centralTailProduct n (upperTailLength c n) := by
  let D : ℕ := centralAnchorDivisor n
    (centralAnchorCutoff depth n) certificate.q
  let B : ℕ := R.prechargeBaseStateProduct
  let donor : ℕ := R.prechargeDonorSet.prod id
  let T : ℕ := centralTailProduct n (upperTailLength c n)
  have hD : 0 < D := by
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  have hB : 0 < B := by
    dsimp [B, BankPaperRealization.prechargeBaseStateProduct]
    apply Finset.prod_pos
    intro factor hfactor
    have hinterval := R.prechargeBaseState_subset_factorInterval hfactor
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1
  have hdonor : 0 < donor := by
    dsimp [donor]
    apply Finset.prod_pos
    intro factor hfactor
    exact Nat.zero_lt_of_lt
      (Finset.mem_Ioc.mp (R.prechargeDonorSet_subset_tail hfactor)).1
  have hT : 0 < T := by
    exact centralTailProduct_pos n (upperTailLength c n)
  have hdonorDvd : donor ∣ T := by
    exact R.prechargeDonorSet_prod_dvd_centralTailProduct
  have hDhigh : ∀ p, p.Prime → yNat n < p →
      D.factorization p = 0 := by
    intro p hp hpHigh
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpDvd
    have hpPrefix := certificate.divisor_prime_support p hp hpDvd
    have hpLe : p ≤ 2 * depth + 1 := (mem_primesUpTo.mp hpPrefix).2
    omega
  have hbaseDonor : ∀ p, p.Prime → yNat n < p →
      B.factorization p = donor.factorization p := by
    intro p _hp hpHigh
    exact R.prechargeBaseStateProduct_factorization_eq_donorSet_prod
      hpHigh
  exact mul_dvd_of_factorization_split_with_donor
    hD hB hdonor hT hdonorDvd hDhigh hbaseDonor hlow

end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperExactificationState -/
section


/-!
# The actual paper bank as a two-state exactification bank

`BankPaperPaths` orients a downward slot from state zero to state one, so its
change is `-e_p`; the generic exactification interface instead calls the
left-hand signed family `+e_p`.  We therefore pair each generic slot with the
actual slot of the opposite orientation.  Boolean state `false` remains the
paper's precharged path state zero and state `true` remains path state one.
This simultaneously aligns signs and keeps the base product equal to the
one reserved in the tail.  The file proves the required product change,
complete-row invariance, positivity, and pairwise cross-slot disjointness.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section



@[simp] theorem bankPaperOppositeSlot_fst
    {P : Type*} {beta : P → ℕ} (slot : SignedBankSlot beta) :
    (bankPaperOppositeSlot slot).1 = slot.1 := by
  rcases slot with ⟨p, copy | copy⟩ <;> rfl

@[simp] theorem bankPaperOppositeSlot_involutive
    {P : Type*} {beta : P → ℕ} (slot : SignedBankSlot beta) :
    bankPaperOppositeSlot (bankPaperOppositeSlot slot) = slot := by
  rcases slot with ⟨p, copy | copy⟩ <;> rfl







@[simp] theorem BankPaperRealization.exactificationState_false
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.exactificationState slot false =
      R.pathStateZero (bankPaperOppositeSlot slot) := by
  simp [BankPaperRealization.exactificationState]

@[simp] theorem BankPaperRealization.exactificationState_true
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.exactificationState slot true =
      R.pathStateOne (bankPaperOppositeSlot slot) := by
  simp [BankPaperRealization.exactificationState]



namespace BankPaperRealization



















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargeExactificationBridge -/
section


/-!
# Identification of the precharged state with the exactification base bank

The concrete precharge layer indexes components by the global request type,
whereas guarded exactification takes the union of state zero over signed bank
slots.  These are two presentations of the same finite set.  The opposite-slot
reindexing used to align signed valuation changes is an involution, so it does
not alter the global state-zero union.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section



/-- Every relevant bottom request and every ordinary request occurs in its
unique signed-slot path. -/
theorem bankPaperIndexedPathComponentRequest_surjective {n : ℕ} :
    Function.Surjective
      (bankPaperIndexedPathComponentRequest (n := n)) := by
  intro request
  cases request with
  | inl request =>
      have hmove : request.1.2 ∈
          bankBottomRelevantMoves request.1.1.1 := by
        apply (bankBottomPaperRequestRelevant_iff_mem_moves request.1).mp
        exact (Finset.mem_filter.mp request.property).2
      let move : ↑(bankBottomRelevantMoves request.1.1.1) :=
        ⟨request.1.2, hmove⟩
      refine ⟨⟨request.1.1, Sum.inr move⟩, ?_⟩
      apply congrArg Sum.inl
      apply Subtype.ext
      rfl
  | inr request =>
      refine ⟨⟨request.1.1, Sum.inl request.1.2⟩, ?_⟩
      apply congrArg Sum.inr
      apply Subtype.ext
      rfl

namespace BankPaperRealization

/-- State zero of one actual path component is exactly the orientation-aware
precharge value of its global request. -/
@[simp] theorem pathStateZeroValue_eq_prechargeBaseStateValue
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateZeroValue slot component =
      R.prechargeBaseStateValue
        (bankPaperPathComponentRequest slot component) := by
  cases component <;> rfl

/-- The generic exactification base bank is literally the paper's precharged
base state.  The orientation swap only permutes the signed slots. -/
theorem baseExactificationBank_eq_prechargeBaseState
    {n M : ℕ} (R : BankPaperRealization n M) :
    baseBankFactors R.exactificationState = R.prechargeBaseState := by
  classical
  ext factor
  constructor
  · intro hfactor
    rw [baseBankFactors, chosenBankFactors, Finset.mem_biUnion] at hfactor
    obtain ⟨slot, _hslot, hstate⟩ := hfactor
    rw [R.exactificationState_false, pathStateZero, indexedPathState,
      Finset.mem_image] at hstate
    obtain ⟨component, _hcomponent, hvalue⟩ := hstate
    rw [prechargeBaseState, indexedPathState, Finset.mem_image]
    refine ⟨bankPaperPathComponentRequest
      (bankPaperOppositeSlot slot) component, Finset.mem_univ _, ?_⟩
    exact (R.pathStateZeroValue_eq_prechargeBaseStateValue
      (bankPaperOppositeSlot slot) component).symm.trans hvalue
  · intro hfactor
    rw [prechargeBaseState, indexedPathState, Finset.mem_image] at hfactor
    obtain ⟨request, _hrequest, hvalue⟩ := hfactor
    obtain ⟨⟨slot, component⟩, hrequestIndex⟩ :=
      bankPaperIndexedPathComponentRequest_surjective request
    rw [← hrequestIndex] at hvalue
    have hcomponentValue :
        R.pathStateZeroValue slot component = factor := by
      exact (R.pathStateZeroValue_eq_prechargeBaseStateValue
        slot component).trans hvalue
    have hstate : factor ∈ R.pathStateZero slot := by
      rw [pathStateZero, indexedPathState, Finset.mem_image]
      exact ⟨component, Finset.mem_univ _, hcomponentValue⟩
    have hstateOpposite : factor ∈
        R.exactificationState (bankPaperOppositeSlot slot) false := by
      simpa only [R.exactificationState_false,
        bankPaperOppositeSlot_involutive] using hstate
    rw [baseBankFactors, chosenBankFactors, Finset.mem_biUnion]
    exact ⟨bankPaperOppositeSlot slot, Finset.mem_univ _, hstateOpposite⟩

/-- Product form of the literal base-state identification. -/
theorem baseExactificationBank_prod_eq_prechargeBaseStateProduct
    {n M : ℕ} (R : BankPaperRealization n M) :
    (baseBankFactors R.exactificationState).prod id =
      R.prechargeBaseStateProduct := by
  rw [R.baseExactificationBank_eq_prechargeBaseState]
  rfl





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargedTailTarget -/
section


/-!
# The residual target after the guarded anchor charge

This file names the exact natural-number target passed to fractional
selection and guarded exactification.  Combined divisibility of the guarded
anchor divisor and the precharged bank immediately shows that the generic
exactification base product divides this target.  The final multiplication
identity is division-free.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace GuardedCentralAnchorCertificate



/-- The quotient target is positive. -/
theorem prechargedTailTarget_pos
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    0 < certificate.prechargedTailTarget := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd
      (centralTailProduct_pos n (upperTailLength c n))
      certificate.divisor_dvd_tail
  · exact centralAnchorDivisor_pos certificate.isCofactorChoice

/-- Division-free target identity used by final product assembly. -/
theorem prechargedTailTarget_mul_centralAnchorDivisor
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    certificate.prechargedTailTarget *
        centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q =
      centralTailProduct n (upperTailLength c n) := by
  exact Nat.div_mul_cancel certificate.divisor_dvd_tail

/-- A simultaneous `divisor * bank` charge makes the actual precharge
product divide the residual target. -/
theorem prechargeBaseStateProduct_dvd_prechargedTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hcombined :
      centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
          R.prechargeBaseStateProduct ∣
        centralTailProduct n (upperTailLength c n)) :
    R.prechargeBaseStateProduct ∣ certificate.prechargedTailTarget := by
  exact (Nat.dvd_div_iff_mul_dvd certificate.divisor_dvd_tail).2 hcombined

/-- The exact same divisibility in the generic exactification notation. -/
theorem baseExactificationBank_prod_dvd_prechargedTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hcombined :
      centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
          R.prechargeBaseStateProduct ∣
        centralTailProduct n (upperTailLength c n)) :
    (baseBankFactors R.exactificationState).prod id ∣
      certificate.prechargedTailTarget := by
  rw [R.baseExactificationBank_prod_eq_prechargeBaseStateProduct]
  exact certificate.prechargeBaseStateProduct_dvd_prechargedTailTarget
    R hcombined

end GuardedCentralAnchorCertificate

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

theorem eventually_bankAnchor_fixed_le_yNat (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, B ≤ yNat n :=
  bankAnchor_yNat_tendsto_atTop.eventually (eventually_ge_atTop B)





/-! ## Arithmetic collision kernels -/



namespace BankPaperRealization



/-! ## Literal recovery of the incident cores from actual requests -/





















/-! ## Complete finite collision theorem -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankGuardedCentralAnchorExistence -/
section


/-!
# Eventual central anchors guarded against every realized bank component

The bank is realized first at the paper endpoint.  Its literal marker set is
intersected with the large central-prime set, all those cofactors are changed,
and the `O(yNat²)=o(n/log n)` budget pays for the modification.  The result is
an actual modified anchor family, not a compatibility package.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

/-- Terminal anchor-guard existence statement for the actual combined bank.
The returned certificate retains a positive one-sixth valuation reserve and
its exact divisor divides the literal factorial tail. -/
theorem exists_eventually_bankGuardedCentralAnchorCertificate
    {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ bank : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)),
          Nonempty
            (GuardedCentralAnchorCertificate c depth n
              bank.anchorGuardLeftCore bank.anchorGuardRightCore
              (bank.centralChangedMarkers depth)) := by
  obtain ⟨depth, hdepth, hcentral⟩ :=
    exists_eventually_centralAnchorCertificate hc
  have hdepthOne : 1 ≤ depth := by omega
  have hC0Pos : (0 : ℝ) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hbank := eventually_exists_bankPaperRealization hcPos
  have hendpoint := eventually_upperScaledEndpoint_bounds hcPos
  have hendpointFive :=
    BankPaperRealization.eventually_two_mul_upperEndpoint_le_five_mul hcPos
  have hcost := eventually_bankPaper_changeCost_le_sixth_reserve
    hc hdepthOne
  refine ⟨depth, hdepth, ?_⟩
  filter_upwards [hcentral, hbank, hendpoint, hendpointFive, hcost,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth)]
      with n hcentralN hbankN hendpointN hendpointFiveN hcostN hnCutoff
  obtain ⟨central⟩ := hcentralN
  obtain ⟨bank⟩ := hbankN
  refine ⟨bank, ?_⟩
  apply guardedCentralAnchorCertificate_of_changeCost
    hc hdepthOne hnCutoff central
    (bank.centralChangedMarkers_subset_largeCentralPrimes depth)
    (bank.centralChangedMarker_le_n hendpointN.2)
    (bank.centralChangedMarker_rowOne_avoids_three
      hnCutoff hendpointN.2 hendpointFiveN)
    (hcostN _ bank)

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargeCapacityAlgebra -/
section


/-!
# Numerical capacity algebra for the precharged bank

The abstract low-prime hypothesis in the precharge divisibility theorem can
be discharged from two explicit numerical inputs.  On the fixed support of
the guarded central divisor, its real valuation reserve absorbs the uniform
bank valuation bound.  Outside that support the central divisor has zero
valuation, and a cross-multiplied natural inequality forces enough capacity
in the literal factorial tail.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Cross-multiplied capacity in a literal tail -/

/-- The lower Legendre estimate turns a cross-multiplied numerical capacity
condition into a literal lower bound for the valuation of `(2n,2n+h]`. -/
theorem centralTailProduct_factorization_ge_of_cross_capacity
    {n h p K : ℕ} (hp : p.Prime)
    (hcapacity :
      (p - 1) * (K + Nat.log2 h + 1) ≤ h) :
    K ≤ (centralTailProduct n h).factorization p := by
  rw [centralTailProduct_factorization]
  have hlower := factorialValuationSub_lower_cross
    (a := 2 * n) (h := h) hp
  have hscaled :
      (p - 1) * (K + Nat.log2 h + 1) ≤
        (p - 1) *
          ((2 * n + h).factorial.factorization p -
              (2 * n).factorial.factorization p +
            Nat.log2 h + 1) :=
    hcapacity.trans hlower
  have hwithSlack :
      K + Nat.log2 h + 1 ≤
        (2 * n + h).factorial.factorization p -
            (2 * n).factorial.factorization p +
          Nat.log2 h + 1 :=
    le_of_mul_le_mul_left hscaled
      (Nat.sub_pos_of_lt hp.one_lt)
  exact Nat.le_of_add_le_add_right
    (Nat.le_of_add_le_add_right hwithSlack)

namespace BankPaperRealization

/-! ## A uniform valuation bound at an endpoint below `3n` -/

/-- At any realized endpoint at most `3n`, every prime coordinate of the
complete precharged base product is bounded by the global marker budget
times the literal binary logarithm of `3n`. -/
theorem prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
    {n M p : ℕ} (R : BankPaperRealization n M) (hp : p.Prime)
    (hendpoint : M ≤ 3 * n) :
    (R.prechargeBaseStateProduct).factorization p ≤
      bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) := by
  simpa only [Nat.log2_eq_log_two] using
    (R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget hp).trans
      (Nat.mul_le_mul_left _ (Nat.log_mono_right hendpoint))

end BankPaperRealization

namespace GuardedCentralAnchorCertificate

/-! ## Discharging every low-prime coordinate -/

/-- On the fixed anchor support, split the visible post-guard reserve into
an amount spent on the precharged bank and an amount retained afterwards.
The conclusion keeps the retained amount explicit next to the exact anchor
and bank valuations.  No sign condition on either bookkeeping function is
needed: the pointwise split inequality is the complete hypothesis. -/
theorem precharge_fixedSupport_factorization_add_retainedReserve_le_upperTailValuation
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hendpoint :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n)
    (spent retained : ℕ → ℝ)
    (hbankSpent : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤ spent p)
    (hreserveSplit : ∀ p ∈ primesUpTo (2 * depth + 1),
      retained p + spent p ≤
        (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n) :
    ∀ p ∈ primesUpTo (2 * depth + 1),
      retained p +
          (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p +
            (R.prechargeBaseStateProduct).factorization p : ℕ) : ℝ) ≤
        (upperTailValuation c n p : ℝ) := by
  intro p hpSupport
  have hp := (mem_primesUpTo.mp hpSupport).1
  have hbank :=
    R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
      hp hendpoint
  have hbankReal :
      ((R.prechargeBaseStateProduct).factorization p : ℝ) ≤
        ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) := by
    exact_mod_cast hbank
  have hbankActualSpent :
      ((R.prechargeBaseStateProduct).factorization p : ℝ) ≤ spent p :=
    hbankReal.trans (hbankSpent p hpSupport)
  calc
    retained p +
          (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p +
            (R.prechargeBaseStateProduct).factorization p : ℕ) : ℝ) =
        ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) + retained p +
          ((R.prechargeBaseStateProduct).factorization p : ℝ) := by
      rw [Nat.cast_add]
      ring
    _ ≤ ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) + retained p +
          spent p := by
      linarith
    _ = ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) +
          (retained p + spent p) := by ring
    _ ≤ ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) +
          ((c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n) := by
      have hsplit := hreserveSplit p hpSupport
      linarith
    _ = (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          ((centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q).factorization p : ℝ) := by ring
    _ ≤ (upperTailValuation c n p : ℝ) :=
      certificate.divisor_reserve p hpSupport

/-- A clean symmetric specialization: one twelfth of the original
`c-C0` margin pays for the precharged bank and another twelfth remains
visible after charging both the guarded anchor and the bank. -/
theorem precharge_fixedSupport_factorization_add_twelfthReserve_le_upperTailValuation
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hendpoint :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n)
    (hbankTwelfth : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n) :
    ∀ p ∈ primesUpTo (2 * depth + 1),
      (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p +
            (R.prechargeBaseStateProduct).factorization p : ℕ) : ℝ) ≤
        (upperTailValuation c n p : ℝ) := by
  exact
    certificate.precharge_fixedSupport_factorization_add_retainedReserve_le_upperTailValuation
      R hendpoint
      (fun p ↦
        (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n)
      (fun p ↦
        (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n)
      hbankTwelfth
      (by
        intro p _hpSupport
        ring_nf
        exact le_rfl)

/-- The full low-prime valuation hypothesis follows from exactly two
numerical conditions:

* on the fixed divisor support, the visible real reserve pays the uniform
  bank bound;
* off that support, the cross-multiplied natural tail capacity pays the same
  uniform bank bound.
-/
theorem precharge_lowPrime_factorization_le_centralTailProduct
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hendpoint :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n)
    (hfixedReserve : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n)
    (huniformCapacity : ∀ p, p.Prime → p ≤ yNat n →
      p ∉ primesUpTo (2 * depth + 1) →
        (p - 1) *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) ≤
          upperTailLength c n) :
    ∀ p, p.Prime → p ≤ yNat n →
      (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q).factorization p +
        (R.prechargeBaseStateProduct).factorization p ≤
      (centralTailProduct n
        (upperTailLength c n)).factorization p := by
  intro p hp hpCutoff
  by_cases hpSupport : p ∈ primesUpTo (2 * depth + 1)
  · have hbank :=
      R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
        hp hendpoint
    have hbankReal :
        ((R.prechargeBaseStateProduct).factorization p : ℝ) ≤
          ((bankPaperAnchorMarkerBudget n *
            Nat.log2 (3 * n) : ℕ) : ℝ) := by
      exact_mod_cast hbank
    have hbankReserve :
        ((R.prechargeBaseStateProduct).factorization p : ℝ) ≤
          (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n :=
      hbankReal.trans (hfixedReserve p hpSupport)
    have hcombined :
        (((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p +
            (R.prechargeBaseStateProduct).factorization p : ℕ) : ℝ) ≤
          (upperTailValuation c n p : ℝ) := by
      rw [Nat.cast_add]
      calc
        ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) +
            ((R.prechargeBaseStateProduct).factorization p : ℝ) ≤
            ((centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p : ℝ) +
              ((c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
                secondOrderScale n) := by
          linarith
        _ = (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
                secondOrderScale n +
              ((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p : ℝ) := by ring
        _ ≤ (upperTailValuation c n p : ℝ) :=
          certificate.divisor_reserve p hpSupport
    rw [← upperTailValuation_eq_centralTailProduct_factorization]
    exact_mod_cast hcombined
  · have hdivisorZero :
        (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q).factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpDvd
      exact hpSupport
        (certificate.divisor_prime_support p hp hpDvd)
    rw [hdivisorZero, zero_add]
    exact
      (R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
          hp hendpoint).trans
        (centralTailProduct_factorization_ge_of_cross_capacity hp
          (huniformCapacity p hp hpCutoff hpSupport))

/-- Consequently the guarded anchor divisor times the actual precharged base
product divides the literal upper-tail product.  The only analytic inputs are
the displayed fixed-support real reserve and off-support natural capacity. -/
theorem mul_prechargeBaseStateProduct_dvd_centralTailProduct_of_capacity
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hsupportCutoff : 2 * depth + 1 ≤ yNat n)
    (hendpoint :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n)
    (hfixedReserve : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n)
    (huniformCapacity : ∀ p, p.Prime → p ≤ yNat n →
      p ∉ primesUpTo (2 * depth + 1) →
        (p - 1) *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) ≤
          upperTailLength c n) :
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
        R.prechargeBaseStateProduct ∣
      centralTailProduct n (upperTailLength c n) := by
  apply certificate.mul_prechargeBaseStateProduct_dvd_centralTailProduct
    R hsupportCutoff
  exact certificate.precharge_lowPrime_factorization_le_centralTailProduct
    R hendpoint hfixedReserve huniformCapacity

end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargeAsymptotic -/
section


/-!
# Negligible small-prime cost of the precharged bank

The precharged base product has valuation at most the global marker budget
times one binary logarithm at each prime.  Summing over all primes at most
`yNat` therefore costs at most

`yNat * bankPaperAnchorMarkerBudget * log₂ (3n)`.

This file proves that literal numerical majorant is little-o of the central
second-order scale.  The analytic core is the identity

`y³ log(n) / (n / log(n)) = log(n)² / n^(1/3)`,

followed by the standard fact that every fixed logarithmic power is
little-o of every positive power.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The cubic endpoint ratio -/



/-- The cubic model reduces exactly to `log(n)² / n^(1/3)`. -/
theorem bankPaperPrechargeCubicNormalizedCost_eq
    {n : ℕ} (hn : 1 < n) :
    bankPaperPrechargeCubicNormalizedCost n =
      L n ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hL : 0 < L n := L_pos hn
  have hyPow : y n ^ 3 = (n : ℝ) ^ (2 / 3 : ℝ) := by
    calc
      y n ^ 3 = ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 := rfl
      _ = (n : ℝ) ^ ((2 / 9 : ℝ) * (3 : ℕ)) :=
        (Real.rpow_mul_natCast (Nat.cast_nonneg n)
          (2 / 9 : ℝ) 3).symm
      _ = (n : ℝ) ^ (2 / 3 : ℝ) := by norm_num
  have hpow :
      (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) =
        (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  rw [bankPaperPrechargeCubicNormalizedCost, secondOrderScale,
    show Real.log (n : ℝ) = L n by rfl, hyPow]
  field_simp [hnR.ne', hL.ne',
    (Real.rpow_pos_of_pos hnR (1 / 3 : ℝ)).ne']
  nlinarith

/-- The cubic normalized model tends to zero. -/
theorem bankPaperPrechargeCubicNormalizedCost_tendsto_zero :
    Tendsto bankPaperPrechargeCubicNormalizedCost atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦
        Real.log x ^ (2 : ℝ) / x ^ (1 / 3 : ℝ))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero
  have hnat : Tendsto
      (fun n : ℕ ↦
        Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds 0) := by
    simpa [Real.rpow_natCast] using
      hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simpa [L] using
    (bankPaperPrechargeCubicNormalizedCost_eq hn).symm

/-- Equivalently, `y³ log n` is little-o of the second-order scale. -/
theorem y_cubed_mul_L_isLittleO_secondOrderScale :
    (fun n : ℕ ↦ y n ^ 3 * L n) =o[atTop] secondOrderScale := by
  have hzero : ∀ᶠ n : ℕ in atTop,
      secondOrderScale n = 0 → y n ^ 3 * L n = 0 := by
    filter_upwards [eventually_secondOrderScale_pos] with n hscale hscaleZero
    exact (hscale.ne' hscaleZero).elim
  apply (isLittleO_iff_tendsto' hzero).mpr
  simpa only [bankPaperPrechargeCubicNormalizedCost] using
    bankPaperPrechargeCubicNormalizedCost_tendsto_zero

/-! ## Integral cutoffs and the binary logarithm -/

/-- The integral cutoff is bounded by its real `n^(2/9)` model. -/
theorem bankPaperPrecharge_yNat_isBigO_y :
    (fun n : ℕ ↦ (yNat n : ℝ)) =O[atTop] y := by
  apply IsBigO.of_bound 1
  filter_upwards [] with n
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ yNat n),
    Real.norm_eq_abs, abs_of_nonneg hyNonneg, one_mul]
  exact hyFloor

/-- The literal binary logarithm in the valuation bound is `O(log n)`. -/
theorem natLog_two_three_mul_isBigO_L :
    (fun n : ℕ ↦ (Nat.log 2 (3 * n) : ℝ)) =O[atTop] L := by
  apply IsBigO.of_bound (2 / Real.log 2)
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hnPos : (0 : ℝ) < n := by positivity
  have hlogn : 0 ≤ L n :=
    (L_pos (show 1 < n by omega)).le
  have hlogThree : Real.log 3 ≤ L n := by
    rw [L]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogMul : Real.log (3 * (n : ℝ)) =
      Real.log 3 + L n := by
    rw [L, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnPos.ne']
  have hdepth : (Nat.log 2 (3 * n) : ℝ) ≤
      Real.log (3 * (n : ℝ)) / Real.log 2 := by
    simpa only [Nat.log2_eq_log_two, Nat.cast_mul, Nat.cast_ofNat] using
      Real.log2_le_logb (3 * n)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ Nat.log 2 (3 * n)),
    Real.norm_eq_abs, abs_of_nonneg hlogn]
  rw [hlogMul] at hdepth
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (Nat.log 2 (3 * n) : ℝ) ≤
        (Real.log 3 + L n) / Real.log 2 := hdepth
    _ ≤ (2 / Real.log 2) * L n := by
      apply (div_le_iff₀ hlogTwo).2
      calc
        Real.log 3 + L n ≤ 2 * L n := by linarith
        _ = (2 / Real.log 2) * L n * Real.log 2 := by
          field_simp

/-- The integral cubic-log model is little-o of the central scale. -/
theorem yNat_cubed_mul_natLog_isLittleO_secondOrderScale :
    (fun n : ℕ ↦
      (yNat n : ℝ) ^ 3 * (Nat.log 2 (3 * n) : ℝ))
      =o[atTop] secondOrderScale := by
  have hraw :=
    (((bankPaperPrecharge_yNat_isBigO_y.mul
        bankPaperPrecharge_yNat_isBigO_y).mul
      bankPaperPrecharge_yNat_isBigO_y).mul
        natLog_two_three_mul_isBigO_L)
  have hcubic :
      (fun n : ℕ ↦
        (yNat n : ℝ) ^ 3 * (Nat.log 2 (3 * n) : ℝ))
        =O[atTop] (fun n : ℕ ↦ y n ^ 3 * L n) := by
    apply hraw.congr'
    · exact Eventually.of_forall fun n ↦ by ring
    · exact Eventually.of_forall fun n ↦ by ring
  exact hcubic.trans_isLittleO
    y_cubed_mul_L_isLittleO_secondOrderScale

/-! ## The concrete precharge cost -/

/-- Real-valued form of the literal small-prime cost majorant is little-o
of the second-order scale. -/
theorem bankPaperPrechargeSmallPrimeCost_isLittleO_secondOrderScale :
    (fun n : ℕ ↦
      (yNat n : ℝ) * (bankPaperAnchorMarkerBudget n : ℝ) *
        (Nat.log 2 (3 * n) : ℝ)) =o[atTop] secondOrderScale := by
  have hraw :=
    ((isBigO_refl (fun n : ℕ ↦ (yNat n : ℝ)) atTop).mul
      bankPaperAnchorMarkerBudget_isBigO_yNat_sq).mul
        (isBigO_refl
          (fun n : ℕ ↦ (Nat.log 2 (3 * n) : ℝ)) atTop)
  have hcost :
      (fun n : ℕ ↦
        (yNat n : ℝ) * (bankPaperAnchorMarkerBudget n : ℝ) *
          (Nat.log 2 (3 * n) : ℝ)) =O[atTop]
        (fun n : ℕ ↦
          (yNat n : ℝ) ^ 3 * (Nat.log 2 (3 * n) : ℝ)) := by
    apply hraw.congr'
    · exact Eventually.of_forall fun n ↦ by ring
    · exact Eventually.of_forall fun n ↦ by ring
  exact hcost.trans_isLittleO
    yNat_cubed_mul_natLog_isLittleO_secondOrderScale

/-- The concrete normalized real cost tends to zero. -/
theorem bankPaperPrechargeSmallPrimeCost_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        ((yNat n : ℝ) * (bankPaperAnchorMarkerBudget n : ℝ) *
          (Nat.log 2 (3 * n) : ℝ)) / secondOrderScale n)
      atTop (nhds 0) :=
  (bankPaperPrechargeSmallPrimeCost_isLittleO_secondOrderScale).tendsto_div_nhds_zero



/-- The cast of the literal natural majorant has vanishing normalized cost. -/
theorem bankPaperPrechargeSmallPrimeCostMajorant_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeSmallPrimeCostMajorant n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  simpa only [bankPaperPrechargeSmallPrimeCostMajorant, Nat.cast_mul] using
    bankPaperPrechargeSmallPrimeCost_normalized_tendsto_zero



namespace BankPaperRealization









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargeUniformCapacityAsymptotic -/
section


/-!
# Uniform precharge capacity at every moving small prime

The summed small-prime precharge cost is negligible, but the moving-prime
allocation needs two uniform consequences.  First, the per-prime cost must
fit below an arbitrarily small multiple of `secondOrderScale / (p-1)` for
every prime `p ≤ yNat`.  Second, after adjoining the logarithmic error from
the lower factorial-valuation bound, the total natural cost must fit inside
the actual upper-tail length.

Both statements are derived from the cubic-log majorant proved in
`BankPaperPrechargeAsymptotic`; no new prime-counting input is used here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Uniform per-prime reserve -/

/-- Eventually, the uniform precharge valuation at every moving small prime
fits below any prescribed positive fraction of its natural
`secondOrderScale / (p-1)` capacity. -/
theorem eventually_bankPaperPrecharge_perPrimeCapacity
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ,
      p.Prime → p ≤ yNat n →
        (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) ≤
          delta / (((p - 1 : ℕ) : ℝ)) * secondOrderScale n := by
  have hsmall :=
    bankPaperPrechargeSmallPrimeCostMajorant_normalized_tendsto_zero.eventually
      (eventually_lt_nhds hdelta)
  filter_upwards [hsmall, eventually_secondOrderScale_pos]
      with n hnormalized hscale
  intro p hpPrime hpY
  have hpredNat : p - 1 ≤ yNat n := (Nat.sub_le p 1).trans hpY
  have hpred : (((p - 1 : ℕ) : ℝ)) ≤ (yNat n : ℝ) := by
    exact_mod_cast hpredNat
  have hpredPosNat : 0 < p - 1 := Nat.sub_pos_of_lt hpPrime.one_lt
  have hpredPos : 0 < (((p - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hpredPosNat
  have hmajorant :
      (yNat n : ℝ) *
          (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) ≤
        delta * secondOrderScale n := by
    have hscaled := (div_lt_iff₀ hscale).mp hnormalized
    simpa only [bankPaperPrechargeSmallPrimeCostMajorant,
      Nat.cast_mul, mul_assoc] using hscaled.le
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpredPos).2
  calc
    (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) *
          (((p - 1 : ℕ) : ℝ)) =
        (((p - 1 : ℕ) : ℝ)) *
          (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) :=
      mul_comm _ _
    _ ≤ (yNat n : ℝ) *
          (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hpred (by positivity)
    _ ≤ delta * secondOrderScale n := hmajorant

/-! ## Combined moving-prime capacity cost -/



/-- The natural cubic-log term has vanishing normalized cost. -/
theorem bankPaperPrechargeCubicLogMajorant_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeCubicLogMajorant n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  simpa only [bankPaperPrechargeCubicLogMajorant,
    Nat.cast_mul, Nat.cast_pow] using
      (yNat_cubed_mul_natLog_isLittleO_secondOrderScale).tendsto_div_nhds_zero



/-- The combined universal capacity majorant is negligible. -/
theorem bankPaperPrechargeUniformCapacityMajorant_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeUniformCapacityMajorant n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  have hcubicTwo : Tendsto
      (fun n : ℕ ↦
        2 * ((bankPaperPrechargeCubicLogMajorant n : ℝ) /
          secondOrderScale n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      bankPaperPrechargeCubicLogMajorant_normalized_tendsto_zero.const_mul
        (2 : ℝ)
  have hsum : Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeSmallPrimeCostMajorant n : ℝ) /
            secondOrderScale n +
          2 * ((bankPaperPrechargeCubicLogMajorant n : ℝ) /
            secondOrderScale n))
      atTop (nhds 0) := by
    simpa only [zero_add] using
      bankPaperPrechargeSmallPrimeCostMajorant_normalized_tendsto_zero.add
        hcubicTwo
  apply hsum.congr'
  exact Eventually.of_forall fun n ↦ by
    simp only [bankPaperPrechargeUniformCapacityMajorant,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring



/-- Once the upper tail is at most `n`, the logarithmic remainder and its
extra `+1` are absorbed by twice the cubic-log term. -/
theorem eventually_bankPaperPrechargeUniformCapacityCost_le_majorant
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      bankPaperPrechargeUniformCapacityCost c n ≤
        bankPaperPrechargeUniformCapacityMajorant n := by
  filter_upwards [eventually_upperTailLength_le hc,
      eventually_ge_atTop 1] with n htail hn
  have htailThree : upperTailLength c n ≤ 3 * n := by omega
  have hlogTail : Nat.log2 (upperTailLength c n) ≤
      Nat.log 2 (3 * n) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_mono_right htailThree
  have hlogOne : 1 ≤ Nat.log 2 (3 * n) := by
    calc
      1 = Nat.log 2 2 := by norm_num
      _ ≤ Nat.log 2 (3 * n) := Nat.log_mono_right (by omega)
  have hlogAdd : Nat.log2 (upperTailLength c n) + 1 ≤
      2 * Nat.log 2 (3 * n) := by omega
  have hyCube : yNat n ≤ yNat n ^ 3 :=
    Nat.le_pow (by omega : 0 < 3)
  have hextra :
      yNat n * (Nat.log2 (upperTailLength c n) + 1) ≤
        2 * bankPaperPrechargeCubicLogMajorant n := by
    calc
      yNat n * (Nat.log2 (upperTailLength c n) + 1) ≤
          yNat n * (2 * Nat.log 2 (3 * n)) :=
        Nat.mul_le_mul_left _ hlogAdd
      _ ≤ yNat n ^ 3 * (2 * Nat.log 2 (3 * n)) :=
        Nat.mul_le_mul_right _ hyCube
      _ = 2 * bankPaperPrechargeCubicLogMajorant n := by
        rw [bankPaperPrechargeCubicLogMajorant]
        ring
  rw [bankPaperPrechargeUniformCapacityCost,
    bankPaperPrechargeUniformCapacityMajorant]
  calc
    yNat n *
        (bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) +
          Nat.log2 (upperTailLength c n) + 1) =
        bankPaperPrechargeSmallPrimeCostMajorant n +
          yNat n * (Nat.log2 (upperTailLength c n) + 1) := by
      rw [bankPaperPrechargeSmallPrimeCostMajorant]
      ring
    _ ≤ bankPaperPrechargeSmallPrimeCostMajorant n +
          2 * bankPaperPrechargeCubicLogMajorant n :=
      Nat.add_le_add_left hextra _

/-- The full natural cost used by the moving-prime capacity argument has
vanishing normalized size. -/
theorem bankPaperPrechargeUniformCapacityCost_normalized_tendsto_zero
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeUniformCapacityCost c n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  have hbound :=
    eventually_bankPaperPrechargeUniformCapacityCost_le_majorant hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    bankPaperPrechargeUniformCapacityMajorant_normalized_tendsto_zero
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    exact div_nonneg (by positivity) hscale.le
  · filter_upwards [hbound, eventually_secondOrderScale_pos]
      with n hcost hscale
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcost) hscale.le

/-- Eventually the entire precharge valuation cost plus the logarithmic
lower-cross error fits inside the actual upper-tail length. -/
theorem eventually_bankPaperPrecharge_uniformMovingPrimeCapacity
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      yNat n *
          (bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) +
            Nat.log2 (upperTailLength c n) + 1) ≤
        upperTailLength c n := by
  have hcostSmall :=
    (bankPaperPrechargeUniformCapacityCost_normalized_tendsto_zero hc).eventually
      (eventually_lt_nhds (half_pos hc))
  have htailLarge :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_gt_nhds (half_lt_self hc))
  filter_upwards [hcostSmall, htailLarge,
      eventually_secondOrderScale_pos] with n hcost htail hscale
  have hratio :
      (bankPaperPrechargeUniformCapacityCost c n : ℝ) /
          secondOrderScale n <
        (upperTailLength c n : ℝ) / secondOrderScale n :=
    hcost.trans htail
  have hcast : (bankPaperPrechargeUniformCapacityCost c n : ℝ) ≤
      (upperTailLength c n : ℝ) :=
    ((div_lt_div_iff_of_pos_right hscale).mp hratio).le
  simpa only [bankPaperPrechargeUniformCapacityCost] using
    (by exact_mod_cast hcast :
      bankPaperPrechargeUniformCapacityCost c n ≤ upperTailLength c n)

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargeCapacityEventually -/
section


/-!
# Eventual literal capacity for the guarded anchor and precharged bank

The analytic uniform-capacity estimates discharge every numerical input of
the finite capacity algebra.  Combining them with the actual guarded-anchor
existence theorem produces, at every sufficiently large paper endpoint, a
literal bank realization and certificate for which the guarded central
divisor together with the complete precharged base bank divides the
factorial tail.  Equivalently, the generic exactification base bank divides
the quotient target left after the anchor charge.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section



namespace GuardedCentralAnchorCertificate

/-- A retained real valuation bound beside the anchor and precharged bank
descends exactly to the quotient target left after the anchor charge. -/
theorem prechargeBaseStateProduct_factorization_add_retained_le_prechargedTailTarget
    {c : ℝ} {depth n p : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ} {retained : ℝ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (bank : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hretained :
      retained +
          (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p +
            bank.prechargeBaseStateProduct.factorization p : ℕ) : ℝ) ≤
        (upperTailValuation c n p : ℝ)) :
    retained +
        (bank.prechargeBaseStateProduct.factorization p : ℝ) ≤
      (certificate.prechargedTailTarget.factorization p : ℝ) := by
  have htargetPos : 0 < certificate.prechargedTailTarget :=
    certificate.prechargedTailTarget_pos
  have hdivisorPos :
      0 < centralAnchorDivisor n (centralAnchorCutoff depth n)
        certificate.q :=
    centralAnchorDivisor_pos certificate.isCofactorChoice
  have htailFactorization :
      (centralTailProduct n
          (upperTailLength c n)).factorization p =
        certificate.prechargedTailTarget.factorization p +
          (centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q).factorization p := by
    calc
      (centralTailProduct n
          (upperTailLength c n)).factorization p =
          (certificate.prechargedTailTarget *
            centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p := by
        rw [certificate.prechargedTailTarget_mul_centralAnchorDivisor]
      _ = certificate.prechargedTailTarget.factorization p +
          (centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q).factorization p := by
        rw [Nat.factorization_mul htargetPos.ne' hdivisorPos.ne',
          Finsupp.add_apply]
  have hbound := hretained
  rw [upperTailValuation_eq_centralTailProduct_factorization,
    htailFactorization] at hbound
  simp only [Nat.cast_add] at hbound
  linarith

end GuardedCentralAnchorCertificate

/-- Strengthened terminal precharge output.  One twelfth of the original
`c - C0` reserve pays for the bank on every fixed anchor prime and a second
twelfth remains visible, both before and after passing to the quotient target
left by the anchor charge. -/
theorem exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve
    {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ bank : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)),
          ∃ certificate : GuardedCentralAnchorCertificate c depth n
              bank.anchorGuardLeftCore bank.anchorGuardRightCore
              (bank.centralChangedMarkers depth),
            centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q * bank.prechargeBaseStateProduct ∣
                centralTailProduct n (upperTailLength c n) ∧
              (∀ p ∈ primesUpTo (2 * depth + 1),
                (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n +
                    (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                          certificate.q).factorization p +
                      bank.prechargeBaseStateProduct.factorization p : ℕ) : ℝ) ≤
                  (upperTailValuation c n p : ℝ)) ∧
              (∀ p ∈ primesUpTo (2 * depth + 1),
                (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n +
                    (bank.prechargeBaseStateProduct.factorization p : ℝ) ≤
                  (certificate.prechargedTailTarget.factorization p : ℝ)) ∧
              (baseBankFactors bank.exactificationState).prod id ∣
                certificate.prechargedTailTarget ∧
              certificate.prechargedTailTarget *
                  centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q =
                centralTailProduct n (upperTailLength c n) := by
  have hC0Pos : (0 : ℝ) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hdeltaSixth : (0 : ℝ) < (c - C0) / 6 := by linarith
  have hdeltaTwelfth : (0 : ℝ) < (c - C0) / 12 := by linarith
  obtain ⟨depth, hdepth, hanchors⟩ :=
    exists_eventually_bankGuardedCentralAnchorCertificate hc
  have hperPrimeSixth :=
    eventually_bankPaperPrecharge_perPrimeCapacity hdeltaSixth
  have hperPrimeTwelfth :=
    eventually_bankPaperPrecharge_perPrimeCapacity hdeltaTwelfth
  have hmoving :=
    eventually_bankPaperPrecharge_uniformMovingPrimeCapacity hcPos
  have hendpoint := eventually_upperScaledEndpoint_bounds hcPos
  have hsupport := eventually_bankAnchor_fixed_le_yNat (2 * depth + 1)
  refine ⟨depth, hdepth, ?_⟩
  filter_upwards [hanchors, hperPrimeSixth, hperPrimeTwelfth, hmoving,
      hendpoint, hsupport]
      with n hanchorN hperPrimeSixthN hperPrimeTwelfthN hmovingN
        hendpointN hsupportN
  obtain ⟨bank, hcertificate⟩ := hanchorN
  obtain ⟨certificate⟩ := hcertificate
  have hfixedReserve : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n := by
    intro p hpMem
    have hpData := mem_primesUpTo.mp hpMem
    have hpCutoff : p ≤ yNat n := hpData.2.trans hsupportN
    simpa only [Nat.log2_eq_log_two, div_div] using
      hperPrimeSixthN p hpData.1 hpCutoff
  have hfixedTwelfth : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n := by
    intro p hpMem
    have hpData := mem_primesUpTo.mp hpMem
    have hpCutoff : p ≤ yNat n := hpData.2.trans hsupportN
    simpa only [Nat.log2_eq_log_two, div_div] using
      hperPrimeTwelfthN p hpData.1 hpCutoff
  have huniformCapacity : ∀ p, p.Prime → p ≤ yNat n →
      p ∉ primesUpTo (2 * depth + 1) →
        (p - 1) *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) ≤
          upperTailLength c n := by
    intro p _hpPrime hpCutoff _hpSupport
    have hpPred : p - 1 ≤ yNat n := (Nat.sub_le p 1).trans hpCutoff
    calc
      (p - 1) *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) ≤
          yNat n *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) :=
        Nat.mul_le_mul_right _ hpPred
      _ ≤ upperTailLength c n := by
        simpa only [Nat.log2_eq_log_two] using hmovingN
  have hcombined :
      centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q * bank.prechargeBaseStateProduct ∣
        centralTailProduct n (upperTailLength c n) :=
    certificate.mul_prechargeBaseStateProduct_dvd_centralTailProduct_of_capacity
      bank hsupportN hendpointN.2 hfixedReserve huniformCapacity
  have hretained :=
    certificate.precharge_fixedSupport_factorization_add_twelfthReserve_le_upperTailValuation
      bank hendpointN.2 hfixedTwelfth
  have htargetRetained : ∀ p ∈ primesUpTo (2 * depth + 1),
      (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          (bank.prechargeBaseStateProduct.factorization p : ℝ) ≤
        (certificate.prechargedTailTarget.factorization p : ℝ) := by
    intro p hpMem
    exact
      certificate.prechargeBaseStateProduct_factorization_add_retained_le_prechargedTailTarget
        bank (hretained p hpMem)
  refine ⟨bank, certificate, hcombined, hretained, htargetRetained, ?_, ?_⟩
  · exact certificate.baseExactificationBank_prod_dvd_prechargedTailTarget
      bank hcombined
  · exact certificate.prechargedTailTarget_mul_centralAnchorDivisor

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_011 := by
  exact @Erdos390.WholePaper.exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve
