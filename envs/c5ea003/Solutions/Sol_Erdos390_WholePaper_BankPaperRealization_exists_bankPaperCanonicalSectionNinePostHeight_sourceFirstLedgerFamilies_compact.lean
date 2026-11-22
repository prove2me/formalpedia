-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstLedgerFamilies_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:27:16.665628+00:00
-- url     : https://prove2.me/submissions/171fb9d7-105f-4f4c-a5ef-0725bd4142d8

import Definitions.Def_erdos390_remaining_analytic_propositions_005
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalActualSelectorMassEstimate_of_topFrozenBalancedInitial_compact
import Theorems.Thm_Erdos390_WholePaper_bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO


section
theorem Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalActualSelectorMassEstimate_of_topFrozenBalancedInitial : Erdos390.RemainingAnalyticGoal004_009 := @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalActualSelectorMassEstimate_of_topFrozenBalancedInitial_compact
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

theorem factorialValuationSub_le_div_pred_add_log2
    {a h p : ℕ} (hp : p.Prime) :
    (a + h).factorial.factorization p - a.factorial.factorization p ≤
      h / (p - 1) + Nat.log2 (a + h) := by
  rw [factorialValuationSub_eq_choose_add_factorialValuation]
  have hchoose :
      (Nat.choose (a + h) h).factorization p ≤ Nat.log2 (a + h) := by
    calc
      (Nat.choose (a + h) h).factorization p ≤ Nat.log p (a + h) :=
        Nat.factorization_choose_le_log
      _ ≤ Nat.log 2 (a + h) :=
        Nat.log_anti_left Nat.one_lt_two hp.two_le
      _ = Nat.log2 (a + h) := Nat.log2_eq_log_two.symm
  have hfactorial :
      h.factorial.factorization p ≤ h / (p - 1) :=
    Nat.factorization_factorial_le_div_pred hp h
  omega









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

/-- Exact two-sided version of
`v_p(∏_{a<j≤a+h} j) = h/(p-1) + O(log(a+h))`. -/
theorem factorialValuationSub_twoSided
    {a h p : ℕ} (hp : p.Prime) :
    h ≤ (p - 1) *
        ((a + h).factorial.factorization p - a.factorial.factorization p +
          Nat.log2 h + 1) ∧
      (a + h).factorial.factorization p - a.factorial.factorization p ≤
        h / (p - 1) + Nat.log2 (a + h) := by
  exact ⟨factorialValuationSub_lower_cross hp,
    factorialValuationSub_le_div_pred_add_log2 hp⟩

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



/-- A tail of length at most `n` gives an endpoint at most `3n`. -/
theorem upperEndpoint_le_three_mul {n h : ℕ} (hh : h ≤ n) :
    upperEndpoint n h ≤ 3 * n := by
  simp only [upperEndpoint]
  omega







private theorem log_sq_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

private theorem log_three_mul_natCast_mul_log_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.log (3 * (n : ℝ)) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hconstant :
      Tendsto (fun _n : ℕ ↦ Real.log 3) atTop (nhds (Real.log 3)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          Real.log 3 * (Real.log (n : ℝ) / (n : ℝ)) +
            Real.log (n : ℝ) ^ 2 / (n : ℝ))
        atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hconstant.mul log_natCast_div_natCast_tendsto_zero).add
        log_sq_natCast_div_natCast_tendsto_zero
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnReal]
  ring

private theorem logb_two_three_mul_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.logb 2 (3 * (n : ℝ)) / secondOrderScale n)
      atTop (nhds 0) := by
  have hscaled :
      Tendsto
        (fun n : ℕ ↦
          (1 / Real.log 2) *
            (Real.log (3 * (n : ℝ)) * Real.log (n : ℝ) /
              (n : ℝ)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      log_three_mul_natCast_mul_log_div_natCast_tendsto_zero.const_mul
        (1 / Real.log 2)
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlogN : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos one_lt_two).ne'
  rw [Real.logb, secondOrderScale]
  field_simp

/-- The binary-logarithmic tail error is negligible on the second-order
scale. -/
theorem log2_three_mul_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (Nat.log2 (3 * n) : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    logb_two_three_mul_normalized_tendsto_zero
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (by positivity) (secondOrderScale_pos hn).le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlogBound :
        (Nat.log2 (3 * n) : ℝ) ≤ Real.logb 2 (3 * (n : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        Real.log2_le_logb (3 * n)
    exact div_le_div_of_nonneg_right hlogBound
      (secondOrderScale_pos hn).le

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.UpperTailValuationAsymptotic -/
section


/-!
# Fixed-prime upper-tail valuation asymptotics

The paper's tail has length `ceil (c n / log n)` above `2n`.  The exact
integer two-sided Legendre bounds squeeze its valuation at every fixed prime.
The logarithmic remainder is discharged by `UpperScale`; no valuation limit
is assumed as an input.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section



/-- Real-cast form of the exact integer squeeze, with one common logarithmic
error valid whenever the tail length is at most `n`. -/
theorem upperTailValuation_cast_bounds
    {c : ℝ} {n p : ℕ} (hp : p.Prime)
    (htail : upperTailLength c n ≤ n) :
    (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) -
          ((Nat.log2 (3 * n) : ℝ) + 1) ≤
        (upperTailValuation c n p : ℝ) ∧
      (upperTailValuation c n p : ℝ) ≤
        (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) +
          ((Nat.log2 (3 * n) : ℝ) + 1) := by
  have htwo := factorialValuationSub_twoSided
    (a := 2 * n) (h := upperTailLength c n) (p := p) hp
  have hlowerNat :
      upperTailLength c n ≤ (p - 1) *
        (upperTailValuation c n p +
          Nat.log2 (upperTailLength c n) + 1) := by
    simpa only [upperTailValuation, upperEndpoint] using htwo.1
  have hupperNat :
      upperTailValuation c n p ≤
        upperTailLength c n / (p - 1) +
          Nat.log2 (upperEndpoint n (upperTailLength c n)) := by
    simpa only [upperTailValuation, upperEndpoint] using htwo.2
  have htailThree : upperTailLength c n ≤ 3 * n := by
    omega
  have hendpointThree :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n :=
    upperEndpoint_le_three_mul htail
  have hlogTail :
      Nat.log2 (upperTailLength c n) ≤ Nat.log2 (3 * n) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right htailThree
  have hlogEndpoint :
      Nat.log2 (upperEndpoint n (upperTailLength c n)) ≤
        Nat.log2 (3 * n) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right hendpointThree
  have hpredPosNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hpredPos : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpredPosNat
  have hlowerCast :
      (upperTailLength c n : ℝ) ≤ ((p - 1 : ℕ) : ℝ) *
        ((upperTailValuation c n p : ℝ) +
          (Nat.log2 (upperTailLength c n) : ℝ) + 1) := by
    exact_mod_cast hlowerNat
  have hbaseLower :
      (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
        (upperTailValuation c n p : ℝ) +
          (Nat.log2 (upperTailLength c n) : ℝ) + 1 := by
    apply (div_le_iff₀ hpredPos).2
    simpa only [mul_comm] using hlowerCast
  have hlogTailCast :
      (Nat.log2 (upperTailLength c n) : ℝ) ≤
        (Nat.log2 (3 * n) : ℝ) := by
    exact_mod_cast hlogTail
  have hupperCast :
      (upperTailValuation c n p : ℝ) ≤
        (upperTailLength c n / (p - 1) : ℕ) +
          (Nat.log2 (upperEndpoint n (upperTailLength c n)) : ℝ) := by
    exact_mod_cast hupperNat
  have hdivCast :
      ((upperTailLength c n / (p - 1) : ℕ) : ℝ) ≤
        (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hlogEndpointCast :
      (Nat.log2 (upperEndpoint n (upperTailLength c n)) : ℝ) ≤
        (Nat.log2 (3 * n) : ℝ) := by
    exact_mod_cast hlogEndpoint
  constructor <;> linarith

/-- Divide the finite squeeze by a positive second-order scale. -/
theorem upperTailValuation_normalized_bounds
    {c : ℝ} {n p : ℕ} (hp : p.Prime)
    (htail : upperTailLength c n ≤ n)
    (hscale : 0 < secondOrderScale n) :
    (upperTailLength c n : ℝ) / secondOrderScale n /
          ((p - 1 : ℕ) : ℝ) -
        ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n ≤
      (upperTailValuation c n p : ℝ) / secondOrderScale n ∧
    (upperTailValuation c n p : ℝ) / secondOrderScale n ≤
      (upperTailLength c n : ℝ) / secondOrderScale n /
          ((p - 1 : ℕ) : ℝ) +
        ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n := by
  have hbounds := upperTailValuation_cast_bounds hp htail
  have hpredPos : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  constructor
  · calc
      (upperTailLength c n : ℝ) / secondOrderScale n /
            ((p - 1 : ℕ) : ℝ) -
          ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n =
        ((upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) -
            ((Nat.log2 (3 * n) : ℝ) + 1)) /
          secondOrderScale n := by
            field_simp [hscale.ne', hpredPos.ne']
      _ ≤ (upperTailValuation c n p : ℝ) / secondOrderScale n :=
        div_le_div_of_nonneg_right hbounds.1 hscale.le
  · calc
      (upperTailValuation c n p : ℝ) / secondOrderScale n ≤
          ((upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) +
              ((Nat.log2 (3 * n) : ℝ) + 1)) /
            secondOrderScale n :=
        div_le_div_of_nonneg_right hbounds.2 hscale.le
      _ = (upperTailLength c n : ℝ) / secondOrderScale n /
            ((p - 1 : ℕ) : ℝ) +
          ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n := by
            field_simp [hscale.ne', hpredPos.ne']

/-- The common binary-logarithmic error in the squeeze is negligible. -/
theorem upperTailLogError_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n)
      atTop (nhds 0) := by
  have hone :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / secondOrderScale n)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop secondOrderScale_tendsto_atTop
  simpa only [add_div, add_zero] using
    log2_three_mul_normalized_tendsto_zero.add hone

/-- Paper (4.12): at every fixed prime, the actual factorial-tail valuation
has main term `c/(p-1)` on the scale `n/log n`. -/
theorem upperTailValuation_normalized_tendsto
    {c : ℝ} (hc : 0 < c) {p : ℕ} (hp : p.Prime) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailValuation c n p : ℝ) / secondOrderScale n)
      atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) := by
  have hmain :
      Tendsto
        (fun n : ℕ ↦
          (upperTailLength c n : ℝ) / secondOrderScale n /
            ((p - 1 : ℕ) : ℝ))
        atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) :=
    (upperTailLength_normalized_tendsto hc).div_const
      ((p - 1 : ℕ) : ℝ)
  have hlower :
      Tendsto
        (fun n : ℕ ↦
          (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) -
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n)
        atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) := by
    simpa only [sub_zero] using
      hmain.sub upperTailLogError_normalized_tendsto_zero
  have hupper :
      Tendsto
        (fun n : ℕ ↦
          (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) +
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n)
        atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) := by
    simpa only [add_zero] using
      hmain.add upperTailLogError_normalized_tendsto_zero
  have hbounds :
      ∀ᶠ n : ℕ in atTop,
        (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) -
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n ≤
          (upperTailValuation c n p : ℝ) / secondOrderScale n ∧
        (upperTailValuation c n p : ℝ) / secondOrderScale n ≤
          (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) +
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n := by
    filter_upwards [eventually_upperTailLength_le hc,
      eventually_secondOrderScale_pos] with n htail hscale
    exact upperTailValuation_normalized_bounds hp htail hscale
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower hupper (hbounds.mono fun _ h ↦ h.1)
      (hbounds.mono fun _ h ↦ h.2)









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











/-- Under the paper's interval-size condition, the two raw blocks exhaust
the whole lower interval `(n,2n]`. -/
theorem roughRawCandidateSet_eq_Ioc
    {n h K : ℕ} (hKh : K * h ≤ n) :
    roughRawCandidateSet n h K = Finset.Ioc n (2 * n) := by
  ext a
  simp only [roughRawCandidateSet, roughHighLowerBlock,
    roughBroadLowerBlock, Finset.mem_union, Finset.mem_Ioc]
  omega

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





































/-- The two physical pieces make the raw weight automatically feasible
whenever their two constant levels lie in `[0,1]`. -/
theorem roughHeadCompatibleRawWeight_mem_unitInterval
    {W n h K : ℕ} {α β L : ℝ}
    (hα : 0 ≤ α ∧ α ≤ 1)
    (hβ : 0 ≤ β / L ∧ β / L ≤ 1)
    (a : ℕ) :
    0 ≤ roughHeadCompatibleRawWeight W n h K α β L a ∧
      roughHeadCompatibleRawWeight W n h K α β L a ≤ 1 := by
  by_cases hcop : Nat.Coprime a (roughHeadModulus W)
  · rw [roughHeadCompatibleRawWeight, if_pos hcop]
    by_cases haHigh : a ∈ roughHighLowerBlock n h K
    · have haBroad : a ∉ roughBroadLowerBlock n h K := by
        intro haBroad
        exact Finset.disjoint_left.mp
          (roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K)
          haHigh haBroad
      simpa [roughFiniteIndicator, haHigh, haBroad] using hα
    · by_cases haBroad : a ∈ roughBroadLowerBlock n h K
      · simpa [roughFiniteIndicator, haHigh, haBroad] using hβ
      · simp [roughFiniteIndicator, haHigh, haBroad]
  · simp [roughHeadCompatibleRawWeight, hcop]











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

















/-! ## Tie-lower nearest integers -/









/-- The universal half-unit rounding error. -/
theorem bankPaperNearestIntegerTieLower_abs_sub_le (x : Real) :
    |(bankPaperNearestIntegerTieLower x : Real) - x| ≤ 1 / 2 := by
  have hcell :=
    (bankPaperNearestIntegerTieLower_eq_iff x
      (bankPaperNearestIntegerTieLower x)).1 rfl
  apply abs_le.mpr
  constructor <;> linarith

/-! ## Exact smooth-row quota initialization -/







/-- Exact expression for the initialization error. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_sub_actual
    (mFrozen qTilde : Real) :
    bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde =
      (bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
        (mFrozen + qTilde) := by
  unfold bankPaperCanonicalSmoothInitialActiveMass
  ring

/-- The paper's literal bound `|q0 - qTilde| <= 1/2`. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen qTilde : Real) :
    |bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde| ≤
      1 / 2 := by
  rw [bankPaperCanonicalSmoothInitialActiveMass_sub_actual]
  exact bankPaperNearestIntegerTieLower_abs_sub_le (mFrozen + qTilde)

















/-! ## Exact frozen-height ledger and centered adjustment -/



























/-! ## Literal Section 8 families -/



















/-- Family-level half-unit initialization error. -/
theorem bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
    (mFrozen qTilde : Nat -> Real) (n : Nat) :
    |bankPaperCanonicalSmoothQ0Family mFrozen qTilde n - qTilde n| <=
      1 / 2 :=
  bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen n) (qTilde n)





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





/-! ## Complete rough signatures -/







/-! ## Endpoint and donor injectivity -/





















/-! ## Literal finite states, donor tail, and replacement map -/





















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





















/-! ## Component counts and the base product -/























end BankPaperRealization

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





end GuardedCentralAnchorCertificate

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

/-- Every fixed exceptional factor is a literal upper-tail occurrence. -/
theorem paperFixedExceptionalFactors_subset_tail
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) := by
  simpa only [roughUpperBlock, upperEndpoint] using
    R.paperFixedExceptionalFactors_subset_upperBlock deltaStar



















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



























/-! ## The donor/base row-preserving bijection -/









/-! ## Upper-tail ownership and the postcharge target -/





























/-! ## Exact local discrepancy ledger -/







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











/-! ## The literal three-coordinate local census -/





/-! ## Guarded broad-pool and postcharge capacities -/







/-! ## The single remaining analytic raw-pool input -/





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

/- Source module: Erdos390.WholePaper.BankPaperProposition87ActualDataConnector -/
section


/-!
# Actual paper data at the Proposition 8.7 / guarded-selector interface

The paper does not use the mass-one normalization of the bridge.  Its
literal active weights are the numbers `z_m^0`, and

`q_n = sum_m z_m^0`.

At a clean numerical coordinate the protected frozen layer may overlap the
active layer.  Consequently `q_n` is not, in general, the sum of the whole
guarded selector on the active support.  This module keeps the two layers
separate.  Every guarded candidate is represented by a frozen tag of weight

`preSelector a - activeSeedAmbient a`,

while Proposition 8.7 evolves the active seed.  Thus the protected overlap
is retained exactly and the combined selector at time zero is the supplied
guarded pre-selector.

The single construction still missing from the finite guarded ledger is
named `BankPaperCanonicalActualActiveMeasureConstructor`.  It asks only for
the paper's active-measure realization: the seed has the canonical
barycentric shape, has eventual paper-scale mass at least one, is supported
on the guarded candidates, and is dominated by the already feasible
pre-selector.  Row integrality, target agreement, band balance, support,
pointwise estimates, and prefix estimates are not repeated in this
constructor; they are derived below from the existing guarded selector and
the Proposition 8.7 path.
-/

open Filter Topology Set
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## The literal active mass and its sole construction socket -/













/-- Every active sample coordinate lies in the literal guarded candidate
set selected for the prebridge. -/
theorem bankPaperCanonicalActiveSeed_value_mem_candidates
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (m : D.Sample) : D.value m ∈ candidates := by
  exact H.2.2.1 m











/-! ## The actual scaled bridge data -/









/-! ## Tagged frozen remainder and exact push-forward -/











/-- Summing the ambient push-forward over all guarded candidates recovers
the tagged active mass exactly, even before using value-map injectivity. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    (∑ a ∈ candidates,
      bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a) =
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
    bankPaperCanonicalLiteralActiveMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (bankPaperCanonicalActiveSeed_value_mem_candidates H m)).elim





/-- The total frozen remainder is the pre-selector mass minus the literal
active mass. -/
theorem sum_bankPaperCanonicalActualFrozenWeight
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
      bankPaperCanonicalActualFrozenWeight
        D candidates preSelector activeSeed a) =
      (∑ a ∈ candidates, preSelector a) -
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActualFrozenWeight
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_subtype candidates (fun _ => Iff.rfl)
    (fun a => preSelector a)]
  rw [← Finset.sum_subtype candidates (fun _ => Iff.rfl)
    (fun a => bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a)]
  rw [sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass H]



/-! ## The initial combined selector -/









/-! ## The literal active marked target and endpoint -/













/-! ## Smooth active support and unchanged complete-rough rows -/







/-- Push-forward mass over any finite set containing every active sample
value is the total tagged seed mass. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (support : Finset Nat)
    (hvalues : ∀ m : D.Sample, D.value m ∈ support) :
    (∑ a ∈ support,
      bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a) =
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
    bankPaperCanonicalLiteralActiveMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalues m)).elim

/-- The active seed push-forward vanishes at a coordinate which is not the
value of any active sample tag. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (a : Nat) (ha : forall m : D.Sample, D.value m ≠ a) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a = 0 := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_eq_zero
  intro m _hm
  rw [if_neg (ha m)]













/-! ## Prime support, exact bands, and the derived prefix ledger -/











/-! ## Complete endpoint handoff -/



/-! ## Direct coupling to the guarded continuation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstruction -/
section


/-!
# Constructing the actual active measure and isolating its irreducible fit

The paper's baseline realization has two logically different parts.

* Once a normalized barycentric target and its literal active mass `q_n`
  are fixed, the active coordinates are forced:

  `z_m^0 = q_n * T.baseline.baseWeight m`.

  Their sum is definitionally finite and is proved below to be exactly
  `q_n`.  No analytic or selector input is needed for this part.

* For a *previously fixed* guarded pre-selector, one must still know that
  the pre-selector carries this active mass at every active numerical
  coordinate.  Under the already available head-pattern separation and
  candidate feasibility, this reduces exactly to the coordinatewise
  inequality

  `q_n * T.baseline.baseWeight m <= preSelector (D.value m)`.

The latter is named `BankPaperCanonicalActualCoordinateFit`.  It is the
irreducible coupling absent from `BankPaperCanonicalGuardedSectionNineContinuation`:
that continuation records feasibility, row sums, and prime residuals, but
no pointwise relation between its selector and the later active baseline.

The module also gives a completely unconditional self-selector
construction, proves the guarded-support part from the existing geometry,
and shows that the older guarded bridge selector constructor supplies the
coordinate fit whenever it is instantiated with the literal active-mass
baseline.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## The forced finite active seed -/











/-! ## Canonical finite support and a self-selector witness -/











/-! ## Exact minimization for a fixed guarded pre-selector -/



/-- For the canonical scaled seed, the original constructor is equivalent
to `q >= 1` and the finite placement condition.  In particular its seed
equation is not an independent missing input. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_scaled_iff
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) :
    BankPaperCanonicalActualActiveMeasureConstructor D T candidates
        preSelector (bankPaperCanonicalScaledActiveSeed T q) ↔
      1 <= q ∧
        BankPaperCanonicalActualActivePlacement
          D T candidates preSelector q := by
  unfold BankPaperCanonicalActualActiveMeasureConstructor
    BankPaperCanonicalActualActivePlacement
  rw [bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]
  constructor
  · intro H
    exact ⟨H.1, H.2.2.1, H.2.2.2⟩
  · intro H
    exact ⟨H.1, (fun _m => rfl), H.2.1, H.2.2⟩





/-- Candidate support, nonnegativity of the pre-selector, and coordinate
fit imply full ambient placement.  Coordinates outside the active image
carry zero active mass; head-pattern separation handles the occupied
coordinates without a collision loss. -/
theorem bankPaperCanonicalActualActivePlacement_of_coordinateFit
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a)
    (hfit : BankPaperCanonicalActualCoordinateFit D T preSelector q) :
    BankPaperCanonicalActualActivePlacement
      D T candidates preSelector q := by
  refine ⟨hvalues, ?_⟩
  intro a ha
  by_cases hactive : ∃ m : D.Sample, D.value m = a
  · rcases hactive with ⟨m, rfl⟩
    rw [bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      D T q hsep m]
    exact hfit m
  · have hzero : bankPaperCanonicalActiveSeedAmbientWeight D
        (bankPaperCanonicalScaledActiveSeed T q) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive ⟨m, hma⟩
    rw [hzero]
    exact hselectorNonneg a ha

/-- Under the fixed structural/feasibility facts, full placement is
equivalent to coordinate fit. -/
theorem bankPaperCanonicalActualActivePlacement_iff_coordinateFit
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a) :
    BankPaperCanonicalActualActivePlacement D T candidates preSelector q ↔
      BankPaperCanonicalActualCoordinateFit D T preSelector q := by
  constructor
  · intro H m
    rw [← bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      D T q hsep m]
    exact H.2 (D.value m) (H.1 m)
  · exact bankPaperCanonicalActualActivePlacement_of_coordinateFit
      D T candidates preSelector q hsep hvalues hselectorNonneg

/-- Consequently, once guarded support and selector nonnegativity are
available, the original active-measure constructor is *exactly* `q >= 1`
plus the pointwise coordinate fit. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a) :
    BankPaperCanonicalActualActiveMeasureConstructor D T candidates
        preSelector (bankPaperCanonicalScaledActiveSeed T q) ↔
      1 <= q ∧
        BankPaperCanonicalActualCoordinateFit D T preSelector q := by
  rw [bankPaperCanonicalActualActiveMeasureConstructor_scaled_iff]
  constructor
  · intro H
    exact ⟨H.1,
      (bankPaperCanonicalActualActivePlacement_iff_coordinateFit
        D T candidates preSelector q hsep hvalues hselectorNonneg).mp H.2⟩
  · intro H
    exact ⟨H.1,
      (bankPaperCanonicalActualActivePlacement_iff_coordinateFit
        D T candidates preSelector q hsep hvalues hselectorNonneg).mpr H.2⟩

/-- Direct constructor from the irreducible coordinate fit. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_of_coordinateFit
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hq : 1 <= q) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a)
    (hfit : BankPaperCanonicalActualCoordinateFit D T preSelector q) :
    BankPaperCanonicalActualActiveMeasureConstructor D T candidates
      preSelector (bankPaperCanonicalScaledActiveSeed T q) := by
  exact
    (bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
      D T candidates preSelector q hsep hvalues hselectorNonneg).mpr
        ⟨hq, hfit⟩



/-! ## Guarded geometry and the older bridge-selector constructor -/







/-! ## The literal mass already stored by the paper head simplex -/





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











/-! ## The exact missing analytic ledger -/



/-! ## Nearest-integer initialization preserves the paper scale -/











/-! ## The logarithmically smaller height adjustment -/

/-- The paper's scale `n / log^2 n` tends to infinity. -/
theorem secondOrderScale_div_L_tendsto_atTop :
    Tendsto (fun n : Nat => secondOrderScale n / L n) atTop atTop := by
  have hzero : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (nhds 0) := by
    simpa only [L, Function.comp_apply, id_eq] using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := Real))).tendsto_div_nhds_zero
  have hpos : ∀ᶠ n : Nat in atTop,
      0 < L n ^ 2 / (n : Real) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (pow_pos (L_pos hn) 2) (by positivity)
  have hright : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hnReal : (n : Real) ≠ 0 := by positivity
  apply (eq_div_iff hL.ne').2
  change (L n ^ 2 / (n : Real))⁻¹ * L n = (n : Real) / L n
  rw [inv_div]
  field_simp [hL.ne', hnReal]





/-! ## Full propagation from the minimal missing ledger -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedgerReduction -/
section


/-!
# Reduction of the remaining Section 8 analytic ledger

The analytic quota/height bridge deliberately leaves two estimates in
`BankPaperCanonicalSectionEightAnalyticLedger`.  This file separates all
finite and asymptotic algebra around those estimates from the genuinely
missing paper inputs.

For the active mass, the literal intermediate object is the constant
`betaAct / L` layer on the guarded label-one broad pool.  Its difference
from the raw layer is exactly the same constant times the number of deleted
coordinates.  The natural smooth-guard census envelope

`yNat^2 + bankPaperAnchorMarkerBudget`

is already `o(secondOrderScale)`.  Thus only a census bound for the literal
deleted pool and the post-correction identification with the actual
`qTilde` remain.

For the height, the paper first proves the three baseline relations

* `m0 + qTilde = h + O(N/L)`,
* `Lambda0 = m0 L + O(N)`,
* `logY = h L + O(N)`.

Nearest-integer initialization transfers the first relation from `qTilde`
to `q0`; the displayed identity for `A0` then proves `A0 = O(N)`.  Hence the
height half of the old black-box ledger is reduced exactly to those three
named source estimates.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal guarded smooth base -/





/-- Fixed exceptional factors and donors are in the upper tail, while every
precharged base or alternate state has a nontrivial marker label.  Therefore
only central anchors can delete a coordinate from the label-one raw pool. -/
theorem bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchors
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) :
    bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
        deltaStar W K ⊆ certificate.anchors := by
  classical
  intro a ha
  have haData := Finset.mem_inter.mp ha
  have haRawRow : a ∈ completeRoughRowFiber (yNat n)
      (roughRawCandidateSet n h K) 1 :=
    roughCanonicalBroadCorrectionPool_subset_rawRow
      W n h K (yNat n) 1 haData.2
  have haDeleted : a ∈
      R.roughCanonicalGuardDeletedRow certificate deltaStar K 1 :=
    Finset.mem_inter.mpr ⟨haRawRow, haData.1⟩
  have haSupport :=
    R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
      certificate deltaStar K 1 haDeleted
  rcases Finset.mem_union.mp haSupport with haBefore | haAlternate
  · rcases Finset.mem_union.mp haBefore with haAnchor | haBase
    · exact haAnchor
    · rw [BankPaperRealization.prechargeBaseState, indexedPathState,
        Finset.mem_image] at haBase
      obtain ⟨request, _hrequest, rfl⟩ := haBase
      have hlabel := (mem_completeRoughRowFiber.mp haRawRow).2
      rw [R.prechargeBase_completeRoughLabel_eq_marker] at hlabel
      have hhigh := R.yNat_lt_paperMarker request
      have hy := R.six_le_yNat
      omega
  · rw [BankPaperRealization.prechargeAlternateState, indexedPathState,
      Finset.mem_image] at haAlternate
    obtain ⟨request, _hrequest, rfl⟩ := haAlternate
    have hlabel := (mem_completeRoughRowFiber.mp haRawRow).2
    rw [R.prechargeAlternate_completeRoughLabel_eq_marker] at hlabel
    have hhigh := R.yNat_lt_paperMarker request
    have hy := R.six_le_yNat
    omega



/-- Retaining the original raw-pool membership sharpens the preceding
support theorem to the exact smooth-anchor intersection. -/
theorem bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchorIntersection
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) :
    bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
        deltaStar W K ⊆
      certificate.anchors ∩
        bankPaperCanonicalRawSmoothBasePool W n h K := by
  intro a ha
  exact Finset.mem_inter.mpr
    ⟨bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchors
        R certificate deltaStar W K ha,
      (Finset.mem_inter.mp ha).2⟩

/-- Hence the missing guard count involves only central anchors which
actually lie in the raw head-free smooth base pool. -/
theorem bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchorIntersection
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) :
    (bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
      deltaStar W K).card <=
        (certificate.anchors ∩
          bankPaperCanonicalRawSmoothBasePool W n h K).card :=
  Finset.card_le_card
    (bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchorIntersection
      R certificate deltaStar W K)

/-! ### The smooth central-anchor census -/



/-- Every guarded central anchor in the raw label-one base pool is a promoted
residual anchor whose base prime is at most `yNat`.  Routed large anchors
retain their marker prime in the complete rough label and hence cannot occur
in this row. -/
theorem guardedCentralAnchors_inter_rawSmoothBasePool_subset_smoothResidual
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (W K : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    certificate.anchors ∩ bankPaperCanonicalRawSmoothBasePool W n h K ⊆
      bankPaperCanonicalSmoothResidualAnchorPool n
        (centralAnchorCutoff depth n) (yNat n) := by
  intro a ha
  have hn : 0 < n :=
    (centralAnchorCutoffThreshold_pos depth).trans_le hnCutoff
  have haRawRow : a ∈ completeRoughRowFiber (yNat n)
      (roughRawCandidateSet n h K) 1 :=
    roughCanonicalBroadCorrectionPool_subset_rawRow
      W n h K (yNat n) 1 (Finset.mem_inter.mp ha).2
  have haLabel : completeRoughLabel (yNat n) a = 1 :=
    (mem_completeRoughRowFiber.mp haRawRow).2
  have haAnchor : a ∈ fullCentralAnchors n
      (centralAnchorCutoff depth n) certificate.q := by
    simpa only [certificate.anchors_eq] using (Finset.mem_inter.mp ha).1
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



/-- Pointwise paper-sized bound for the relevant smooth guarded anchors. -/
theorem guardedCentralAnchors_inter_rawSmoothBasePool_card_le_yNat
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (W K : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    (certificate.anchors ∩
      bankPaperCanonicalRawSmoothBasePool W n h K).card <= yNat n :=
  (Finset.card_le_card
    (guardedCentralAnchors_inter_rawSmoothBasePool_subset_smoothResidual
      certificate W K hnCutoff hyCutoff)).trans
    (bankPaperCanonicalSmoothResidualAnchorPool_card_le n
      (centralAnchorCutoff depth n) (yNat n))

/-- Deleting the numerical guards changes the raw active base mass by
exactly `betaAct / L` times the literal deletion cardinality. -/
theorem bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) (betaAct : Real) :
    bankPaperCanonicalRawSmoothBaseMass W n h K betaAct -
        bankPaperCanonicalGuardedSmoothBaseMass R certificate
          deltaStar W K betaAct =
      betaAct / L n *
        ((bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
          deltaStar W K).card : Real) := by
  let rawPool : Finset Nat :=
    bankPaperCanonicalRawSmoothBasePool W n h K
  let guardSet : Finset Nat :=
    R.roughCanonicalGuardSet certificate deltaStar
  change
    betaAct / L n * (rawPool.card : Real) -
        betaAct / L n * ((rawPool \ guardSet).card : Real) =
      betaAct / L n * ((guardSet ∩ rawPool).card : Real)
  have hcard :
      (guardSet ∩ rawPool).card <= rawPool.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hcardDiff :
      ((rawPool \ guardSet).card : Real) =
        (rawPool.card : Real) - ((guardSet ∩ rawPool).card : Real) := by
    rw [Finset.card_sdiff, Nat.cast_sub hcard]
  rw [hcardDiff, mul_sub]
  ring

/-! ## Honest tail families and their total asymptotic extensions -/















/-! ## The already-small guard census envelope -/



/-- The census envelope is pointwise nonnegative. -/
theorem bankPaperCanonicalSmoothGuardCensusEnvelope_nonneg (n : Nat) :
    0 <= bankPaperCanonicalSmoothGuardCensusEnvelope n := by
  unfold bankPaperCanonicalSmoothGuardCensusEnvelope
  positivity

/-- The moving square cutoff is little-o of the central paper scale. -/
theorem bankPaperCanonical_yNat_sq_isLittleO_secondOrderScale :
    (fun n : Nat => (yNat n : Real) ^ 2) =o[atTop]
      secondOrderScale := by
  have hzero : ∀ᶠ n : Nat in atTop,
      secondOrderScale n = 0 -> (yNat n : Real) ^ 2 = 0 := by
    filter_upwards [eventually_secondOrderScale_pos] with n hscale hzero
    exact (hscale.ne' hzero).elim
  apply (isLittleO_iff_tendsto' hzero).mpr
  exact yNat_sq_div_secondOrderScale_tendsto_zero

/-- Consequently the complete smooth-guard census envelope is negligible. -/
theorem bankPaperCanonicalSmoothGuardCensusEnvelope_isLittleO :
    bankPaperCanonicalSmoothGuardCensusEnvelope =o[atTop]
      secondOrderScale := by
  have hsum := bankPaperCanonical_yNat_sq_isLittleO_secondOrderScale.add
    bankPaperAnchorMarkerBudget_isLittleO_secondOrderScale
  exact hsum.congr_left fun n => by
    rfl

/-- Uniformly over every honest tail family of guarded certificates, the
total relevant-anchor extension is `O` of the census envelope.  This closes
the finite guard-deletion census with no new analytic input and no
realization request on the finite prefix. -/
theorem guardedCentralAnchors_inter_rawSmoothBasePool_isBigO_envelope
    {c : Real} {N : Nat} (depth W K : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    F.extendedAnchorIntersectionCard W K =O[atTop]
      bankPaperCanonicalSmoothGuardCensusEnvelope := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop
      (centralAnchorCutoffThreshold depth),
    eventually_yNat_lt_centralAnchorCutoff depth,
    eventually_bankBottom_six_le_yNat] with
      n hnTail hnCutoff hyCutoff hySix
  rw [BankPaperCanonicalGuardedTailFamily.extendedAnchorIntersectionCard,
    dif_pos hnTail, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs,
    abs_of_nonneg (bankPaperCanonicalSmoothGuardCensusEnvelope_nonneg n),
    one_mul]
  have hcard :
      (((BankPaperCanonicalGuardedTailFamily.certificate
          F n hnTail).anchors ∩
        bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) <= (yNat n : Real) := by
    exact_mod_cast
      guardedCentralAnchors_inter_rawSmoothBasePool_card_le_yNat
        (BankPaperCanonicalGuardedTailFamily.certificate F n hnTail)
          W K hnCutoff hyCutoff
  have hyOne : (1 : Real) <= yNat n := by
    exact_mod_cast (show 1 <= yNat n by omega)
  have hyNonneg : (0 : Real) <= yNat n := by positivity
  have hySq : (yNat n : Real) <= (yNat n : Real) ^ 2 := by
    calc
      (yNat n : Real) = (yNat n : Real) * 1 := by ring
      _ <= (yNat n : Real) * (yNat n : Real) :=
        mul_le_mul_of_nonneg_left hyOne hyNonneg
      _ = (yNat n : Real) ^ 2 := by ring
  exact hcard.trans <| hySq.trans <|
    le_add_of_nonneg_right (by positivity)



/-- Every family satisfying the named finite census is automatically
little-o of the paper scale. -/
theorem bankPaperCanonicalSmoothGuardDeletionCard_isLittleO
    (deletedCard : Nat -> Real)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard) :
    deletedCard =o[atTop] secondOrderScale :=
  Hcensus.trans_isLittleO
    bankPaperCanonicalSmoothGuardCensusEnvelope_isLittleO

/-- For fixed `betaAct`, the coefficient `betaAct / L` is uniformly
bounded. -/
theorem bankPaperCanonical_beta_div_L_isBigO_one (betaAct : Real) :
    (fun n : Nat => betaAct / L n) =O[atTop]
      (fun _n : Nat => (1 : Real)) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLone : ∀ᶠ n : Nat in atTop, 1 <= L n :=
    hLTop.eventually (eventually_ge_atTop (1 : Real))
  apply IsBigO.of_bound ‖betaAct‖
  filter_upwards [hLone] with n hn
  have hnormL : 1 <= ‖L n‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hn)]
    exact hn
  rw [norm_div, norm_one, mul_one]
  exact div_le_self (norm_nonneg betaAct) hnormL

/-- A census-sized family of deleted coordinates has negligible weighted
mass under the literal `betaAct / L` base layer. -/
theorem bankPaperCanonicalSmoothGuardDeletionMass_isLittleO
    (betaAct : Real) (deletedCard : Nat -> Real)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard) :
    (fun n => betaAct / L n * deletedCard n) =o[atTop]
      secondOrderScale := by
  have hweighted :=
    (bankPaperCanonical_beta_div_L_isBigO_one betaAct).mul_isLittleO
      (bankPaperCanonicalSmoothGuardDeletionCard_isLittleO
        deletedCard Hcensus)
  simpa only [one_mul] using hweighted



/-- Exact identities plus the finite deletion census transfer the raw base
to the explicit guarded base at little-o cost. -/
theorem bankPaperCanonicalRawSmoothBase_sub_guarded_isLittleO_of_census
    (betaAct : Real) (rawBase guardedBase deletedCard : Nat -> Real)
    (hidentity : forall n,
      rawBase n - guardedBase n =
        betaAct / L n * deletedCard n)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard) :
    (fun n => rawBase n - guardedBase n) =o[atTop]
      secondOrderScale := by
  exact (bankPaperCanonicalSmoothGuardDeletionMass_isLittleO
    betaAct deletedCard Hcensus).congr_left fun n =>
      (hidentity n).symm

/-- The first field of `BankPaperCanonicalSectionEightAnalyticLedger`
follows from the literal raw-to-guarded identity, the finite census, and the
single named guarded-to-actual correction estimate. -/
theorem bankPaperCanonicalRawSmoothBase_sub_qTilde_isLittleO_of_guardedReduction
    (betaAct : Real)
    (rawBase guardedBase qTilde deletedCard : Nat -> Real)
    (hidentity : forall n,
      rawBase n - guardedBase n =
        betaAct / L n * deletedCard n)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard)
    (Hcorrection : BankPaperCanonicalGuardedSmoothCorrectionEstimate
      guardedBase qTilde) :
    (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale := by
  have hguard :=
    bankPaperCanonicalRawSmoothBase_sub_guarded_isLittleO_of_census
      betaAct rawBase guardedBase deletedCard hidentity Hcensus
  exact (hguard.add Hcorrection).congr_left fun n => by ring

/-! ## Reduction of the frozen height defect -/



/-- Constants are `O(N/L)` because the logarithmically smaller scale tends
to infinity. -/
theorem bankPaperCanonical_one_isBigO_secondOrderScale_div_L :
    (fun _n : Nat => (1 : Real)) =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  apply IsBigO.of_bound 1
  have hlarge := secondOrderScale_div_L_tendsto_atTop.eventually
    (eventually_ge_atTop (1 : Real))
  filter_upwards [hlarge] with n hn
  have hnonneg : 0 <= secondOrderScale n / L n :=
    zero_le_one.trans hn
  simpa only [norm_one, one_mul, Real.norm_eq_abs,
    abs_of_nonneg hnonneg] using hn

/-- The nearest-integer change from `qTilde` to `q0` preserves the baseline
mass estimate at the smaller `N/L` scale. -/
theorem bankPaperCanonicalSmoothQ0_baselineMassError_isBigO
    (h m0 mFrozen qTilde : Nat -> Real)
    (Hmass : (fun n => m0 n + qTilde n - h n) =O[atTop]
      (fun n => secondOrderScale n / L n)) :
    (fun n => m0 n +
        bankPaperCanonicalSmoothQ0Family mFrozen qTilde n - h n)
      =O[atTop] (fun n => secondOrderScale n / L n) := by
  have hroundOne :
      (fun n => bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
        qTilde n) =O[atTop] (fun _n : Nat => (1 : Real)) := by
    apply IsBigO.of_bound (1 / 2)
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
        mFrozen qTilde n
  have hround := hroundOne.trans
    bankPaperCanonical_one_isBigO_secondOrderScale_div_L
  exact (Hmass.add hround).congr_left fun n => by ring

/-- Multiplying the baseline mass error `O(N/L)` by `L` gives `O(N)`. -/
theorem bankPaperCanonicalSmoothQ0_baselineMassError_mul_L_isBigO
    (h m0 mFrozen qTilde : Nat -> Real)
    (Hmass : (fun n => m0 n + qTilde n - h n) =O[atTop]
      (fun n => secondOrderScale n / L n)) :
    (fun n => (m0 n +
        bankPaperCanonicalSmoothQ0Family mFrozen qTilde n - h n) * L n)
      =O[atTop] secondOrderScale := by
  have hmassQ0 := bankPaperCanonicalSmoothQ0_baselineMassError_isBigO
    h m0 mFrozen qTilde Hmass
  have hraw := hmassQ0.mul (isBigO_refl L atTop)
  apply hraw.congr' EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 1] with n hn
  exact div_mul_cancel₀ (secondOrderScale n) (L_pos hn).ne'

/-- The paper's three baseline estimates imply the literal frozen height
defect bound, with all signs exposed by the exact algebraic identity. -/
theorem bankPaperCanonicalSmoothA0Family_isBigO_of_baselineSource
    (h logY Lambda0 m0 mFrozen qTilde : Nat -> Real)
    (Hsource : BankPaperCanonicalFrozenBaselineSourceLedger
      h logY Lambda0 m0 qTilde) :
    bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen qTilde
      =O[atTop] secondOrderScale := by
  have hmassL :=
    bankPaperCanonicalSmoothQ0_baselineMassError_mul_L_isBigO
      h m0 mFrozen qTilde Hsource.1
  have hsum := (Hsource.2.2.sub Hsource.2.1).sub hmassL
  exact hsum.congr_left fun n => by
    unfold bankPaperCanonicalSmoothA0Family
    unfold bankPaperCanonicalSmoothFrozenHeightDefect
    ring

/-! ## The complete reduced source ledger -/



/-- Main reduction theorem: the smaller paper-facing source ledger, together
with the already-proved raw-to-guarded finite identity, constructs the old
two-field Section 8 analytic ledger. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_sourceLedger
    (betaAct : Real)
    (rawBase guardedBase qTilde deletedCard : Nat -> Real)
    (h logY Lambda0 m0 mFrozen : Nat -> Real)
    (hidentity : forall n,
      rawBase n - guardedBase n =
        betaAct / L n * deletedCard n)
    (Hsource : BankPaperCanonicalSectionEightAnalyticSourceLedger
      guardedBase qTilde deletedCard h logY Lambda0 m0) :
    BankPaperCanonicalSectionEightAnalyticLedger rawBase qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde) := by
  constructor
  · exact
      bankPaperCanonicalRawSmoothBase_sub_qTilde_isLittleO_of_guardedReduction
        betaAct rawBase guardedBase qTilde deletedCard hidentity
          Hsource.1 Hsource.2.1
  · exact bankPaperCanonicalSmoothA0Family_isBigO_of_baselineSource
      h logY Lambda0 m0 mFrozen qTilde Hsource.2.2

/-- Literal-bank specialization of the main reduction for an honest tail
family.  The chosen total extensions make the raw-to-guarded identity exact
both on the realized tail and on its synthetic finite prefix, so every field
of `Hsource` is a genuine asymptotic source estimate. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_literalGuardedSource
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (qTilde h logY Lambda0 m0 mFrozen : Nat -> Real)
    (Hsource : BankPaperCanonicalSectionEightAnalyticSourceLedger
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      qTilde
      (F.extendedSmoothBaseGuardDeletionCard W K deltaStar)
      h logY Lambda0 m0) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde) := by
  apply bankPaperCanonicalSectionEightAnalyticLedger_of_sourceLedger
    betaAct
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
    qTilde
    (F.extendedSmoothBaseGuardDeletionCard W K deltaStar)
    h logY Lambda0 m0 mFrozen
  · intro n
    by_cases hn : N ≤ n
    · simpa only [
          BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
          BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
          dif_pos hn] using
        bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion
          (BankPaperCanonicalGuardedTailFamily.realization F n hn)
          (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
            deltaStar W K betaAct
    · simp only [
        BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
        BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
        dif_neg hn, sub_self, mul_zero]
  · exact Hsource

/-- Fully reduced tail-family specialization.  The finite support theorem
above turns an `O(yNat^2 + markerBudget)` census for the relevant smooth
anchors into the required deletion census.  Thus no precharge, donor, fixed-
exceptional, or alternate-state cardinality remains in the source data. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_literalAnchorSource
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (qTilde h logY Lambda0 m0 mFrozen : Nat -> Real)
    (Hanchors :
      F.extendedAnchorIntersectionCard W K =O[atTop]
        bankPaperCanonicalSmoothGuardCensusEnvelope)
    (Hcorrection : BankPaperCanonicalGuardedSmoothCorrectionEstimate
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      qTilde)
    (Hbaseline : BankPaperCanonicalFrozenBaselineSourceLedger
      h logY Lambda0 m0 qTilde) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde) := by
  have hdeletedToAnchors :
      F.extendedSmoothBaseGuardDeletionCard W K deltaStar =O[atTop]
        F.extendedAnchorIntersectionCard W K := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [
      BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
      dif_pos hn,
      BankPaperCanonicalGuardedTailFamily.extendedAnchorIntersectionCard,
      dif_pos hn, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
    exact_mod_cast
      bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchorIntersection
        (BankPaperCanonicalGuardedTailFamily.realization F n hn)
        (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
          deltaStar W K
  have Hdeleted : BankPaperCanonicalSmoothGuardDeletionCensus
      (F.extendedSmoothBaseGuardDeletionCard W K deltaStar) :=
    hdeletedToAnchors.trans Hanchors
  apply
    bankPaperCanonicalSectionEightAnalyticLedger_of_literalGuardedSource
      depth W K betaAct deltaStar F qTilde h logY Lambda0 m0 mFrozen
  exact ⟨Hdeleted, Hcorrection, Hbaseline⟩

/-- Final tail-family reduction with the guard census discharged.  The first
old ledger field now requires only the extended guarded-to-`qTilde`
correction estimate; the second requires exactly the paper's three baseline
mass/height estimates. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_correctionAndBaseline
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (qTilde h logY Lambda0 m0 mFrozen : Nat -> Real)
    (Hcorrection : BankPaperCanonicalGuardedSmoothCorrectionEstimate
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      qTilde)
    (Hbaseline : BankPaperCanonicalFrozenBaselineSourceLedger
      h logY Lambda0 m0 qTilde) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde) := by
  apply bankPaperCanonicalSectionEightAnalyticLedger_of_literalAnchorSource
    depth W K betaAct deltaStar F qTilde h logY Lambda0 m0 mFrozen
  · exact guardedCentralAnchors_inter_rawSmoothBasePool_isBigO_envelope
      depth W K F
  · exact Hcorrection
  · exact Hbaseline

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







/-! ## Exact support cutoff for the actual fixed charge -/







/-! ## Closing the finite weighted Selberg estimate -/













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





/-- The actual-data split identifies the total frozen mass with the fixed
integral count plus candidate selector mass minus literal active mass. -/
theorem bankPaperCanonicalActualFrozenTotalMass_eq
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    bankPaperCanonicalActualFrozenTotalMass
        D fixed bankBase candidates preSelector activeSeed =
      (fixed.card : Real) + (bankBase.card : Real) +
        (∑ a ∈ candidates, preSelector a) -
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  unfold bankPaperCanonicalActualFrozenTotalMass
  rw [sum_bankPaperCanonicalActualFrozenWeight H]
  ring

/-- Equivalently, adjoining the literal active mass recovers the complete
fixed-plus-selector mass with no error term. -/
theorem bankPaperCanonicalActualFrozenTotalMass_add_literalActiveMass_eq
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    bankPaperCanonicalActualFrozenTotalMass
          D fixed bankBase candidates preSelector activeSeed +
        bankPaperCanonicalLiteralActiveMass D activeSeed =
      (fixed.card : Real) + (bankBase.card : Real) +
        ∑ a ∈ candidates, preSelector a := by
  rw [bankPaperCanonicalActualFrozenTotalMass_eq
    D T fixed bankBase candidates preSelector activeSeed H]
  ring

/-! ## Families of literal actual data -/





/-! ## Elementary logarithmic geometry of the literal upper tail -/





/-- The logarithm of the central tail product is the sum of the logarithms
of its literal factors. -/
theorem bankPaperCanonicalCentralTailLog_eq_sum (n h : Nat) :
    Real.log (centralTailProduct n h : Real) =
      ∑ a ∈ factorInterval (2 * n) (2 * n + h),
        Real.log (a : Real) := by
  unfold centralTailProduct
  rw [Nat.cast_prod]
  apply Real.log_prod
  intro a ha
  have haPos : 0 < a := by
    have haBounds := Finset.mem_Ioc.mp ha
    omega
  exact_mod_cast haPos.ne'

/-- Exact centered-log identity for the complete central tail. -/
theorem bankPaperCanonicalCentralTailLog_sub_height_mul_L_eq_sum
    (n h : Nat) :
    Real.log (centralTailProduct n h : Real) - (h : Real) * L n =
      ∑ a ∈ factorInterval (2 * n) (2 * n + h),
        (Real.log (a : Real) - L n) := by
  rw [bankPaperCanonicalCentralTailLog_eq_sum,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard : (factorInterval (2 * n) (2 * n + h)).card = h := by
    simp only [factorInterval, Nat.card_Ioc]
    omega
  rw [hcard]

/-- Every factor in `(n,2n+h]`, when `h <= n`, has logarithmic displacement
from `log n` between zero and `log 3`. -/
theorem bankPaperCanonicalFactorLog_sub_L_mem_Icc
    {n h a : Nat} (hn : 0 < n) (hh : h <= n)
    (ha : a ∈ factorInterval n (upperEndpoint n h)) :
    Real.log (a : Real) - L n ∈ Set.Icc (0 : Real) (Real.log 3) := by
  have haBounds := Finset.mem_Ioc.mp ha
  have hnLeA : n <= a := haBounds.1.le
  have haLeThree : a <= 3 * n :=
    haBounds.2.trans (upperEndpoint_le_three_mul hh)
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have haReal : 0 < (a : Real) := by
    exact_mod_cast (hn.trans_le hnLeA)
  have hlower : L n <= Real.log (a : Real) := by
    rw [L]
    exact Real.log_le_log hnReal (by exact_mod_cast hnLeA)
  have hupper : Real.log (a : Real) <= Real.log 3 + L n := by
    calc
      Real.log (a : Real) <= Real.log (3 * (n : Real)) :=
        Real.log_le_log haReal (by exact_mod_cast haLeThree)
      _ = Real.log 3 + L n := by
        rw [L, Real.log_mul (by norm_num : (3 : Real) ≠ 0) hnReal.ne']
  exact ⟨sub_nonneg.mpr hlower, by linarith⟩



/-- The complete central-tail logarithm differs from `h log n` by only
`O(secondOrderScale)`.  This is elementary: there are exactly `h` factors,
and each lies between `n` and `3n`. -/
theorem bankPaperCanonicalCentralTailLogTarget_sub_height_mul_L_isBigO
    {c : Real} (hc : 0 < c) :
    (fun n => bankPaperCanonicalCentralTailLogTarget c n -
      bankPaperCanonicalUpperTailHeight c n * L n) =O[atTop]
        secondOrderScale := by
  apply IsBigO.of_bound (2 * c * Real.log 3)
  filter_upwards [eventually_gt_atTop 0, eventually_upperTailLength_le hc,
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc,
      eventually_secondOrderScale_pos]
      with n hn htail htailScale hscale
  let h := upperTailLength c n
  have hlogThree : 0 <= Real.log 3 := Real.log_nonneg (by norm_num)
  have hpoint : ∀ a ∈ factorInterval (2 * n) (2 * n + h),
      Real.log (a : Real) - L n ∈ Set.Icc (0 : Real) (Real.log 3) := by
    intro a ha
    apply bankPaperCanonicalFactorLog_sub_L_mem_Icc hn htail
    rw [factorInterval] at ha ⊢
    rw [Finset.mem_Ioc] at ha ⊢
    constructor
    · omega
    · simpa only [upperEndpoint] using ha.2
  have hsumNonneg : 0 <=
      ∑ a ∈ factorInterval (2 * n) (2 * n + h),
        (Real.log (a : Real) - L n) := by
    apply Finset.sum_nonneg
    intro a ha
    exact (hpoint a ha).1
  have hcard : (factorInterval (2 * n) (2 * n + h)).card = h := by
    simp only [factorInterval, Nat.card_Ioc]
    omega
  rw [bankPaperCanonicalCentralTailLogTarget,
    bankPaperCanonicalUpperTailHeight,
    bankPaperCanonicalCentralTailLog_sub_height_mul_L_eq_sum,
    Real.norm_eq_abs, abs_of_nonneg hsumNonneg,
    Real.norm_eq_abs, abs_of_pos hscale]
  calc
    (∑ a ∈ factorInterval (2 * n) (2 * n + h),
        (Real.log (a : Real) - L n)) <=
        ∑ _a ∈ factorInterval (2 * n) (2 * n + h),
          Real.log 3 := by
      apply Finset.sum_le_sum
      intro a ha
      exact (hpoint a ha).2
    _ = (h : Real) * Real.log 3 := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ <= (2 * c * secondOrderScale n) * Real.log 3 :=
      mul_le_mul_of_nonneg_right htailScale hlogThree
    _ = (2 * c * Real.log 3) * secondOrderScale n := by ring

/-! ## Centering the literal frozen logarithmic ledger -/















/-! ## Exact charged-selector row ledger -/



































/-! ## The remaining actual analytic sources -/



/-- The actual-data estimate is exactly the generic guarded-correction
estimate with `qTilde` instantiated by the literal tagged seed mass. -/
theorem bankPaperCanonicalGuardedSmoothCorrectionEstimate_of_actualData
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (activeSeed : forall n, (D n).Sample -> Real)
    (guardedBase : Nat -> Real)
    (H : BankPaperCanonicalActualGuardedSmoothMassEstimate
      D activeSeed guardedBase) :
    BankPaperCanonicalGuardedSmoothCorrectionEstimate guardedBase
      (bankPaperCanonicalLiteralQMass D activeSeed) :=
  H

/-- For the canonical scaled active seed, the active-mass identification is
exact: its literal mass is the chosen guarded-base mass.  Thus the first
analytic source estimate disappears entirely for this paper-facing choice. -/
theorem bankPaperCanonicalActualGuardedSmoothMassEstimate_scaledActiveSeed
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (guardedBase : Nat -> Real) :
    BankPaperCanonicalActualGuardedSmoothMassEstimate D
      (fun n => bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n))
      guardedBase := by
  have hzero : (fun _n : Nat => (0 : Real)) =o[atTop]
      secondOrderScale := isLittleO_zero _ _
  exact hzero.congr_left fun n => by
    simp only [bankPaperCanonicalLiteralQMass,
      bankPaperCanonicalLiteralActiveMass_scaledActiveSeed, sub_self]



/-- For the literal central-tail target, interval geometry derives both
logarithmic fields of the baseline ledger.  This generic adapter accepts a
selector total-mass estimate; the constructed-quota closure below proves it. -/
theorem bankPaperCanonicalActualFrozenBaselineEstimates_of_intervalGeometry
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} (hc : 0 < c)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates)
    (Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates preSelector) :
    BankPaperCanonicalActualFrozenBaselineEstimates
      D fixed bankBase candidates preSelector activeSeed
        (bankPaperCanonicalUpperTailHeight c)
        (bankPaperCanonicalCentralTailLogTarget c) := by
  exact ⟨Hselector,
    bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO
      hc D T fixed bankBase candidates preSelector activeSeed Hconstructor
        Hgeometry Hselector,
    bankPaperCanonicalCentralTailLogTarget_sub_height_mul_L_isBigO hc⟩





/-- Central-tail specialization of the actual source ledger.  Active mass is
exact for the scaled seed and both logarithmic estimates are theorems.  Its
generic selector-mass input is discharged by the constructed-quota closure. -/
theorem bankPaperCanonicalSectionEightScaledActualDataSourceLedger_of_intervalGeometry
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} (hc : 0 < c)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (guardedBase : Nat -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n)
          (bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n)))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates)
    (Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates preSelector) :
    BankPaperCanonicalSectionEightScaledActualDataSourceLedger
      D T fixed bankBase candidates preSelector guardedBase
        (bankPaperCanonicalUpperTailHeight c)
        (bankPaperCanonicalCentralTailLogTarget c) := by
  exact ⟨Hconstructor,
    bankPaperCanonicalActualFrozenBaselineEstimates_of_intervalGeometry
      hc D T fixed bankBase candidates preSelector
        (fun n => bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n))
        Hconstructor Hgeometry Hselector⟩

/-! ## Construction of the old Section 8 ledger -/

/-- The literal actual estimates construct the frozen-baseline source
ledger.  Its first field is just the exact active/frozen decomposition
followed by the supplied total-selector estimate. -/
theorem bankPaperCanonicalFrozenBaselineSourceLedger_of_actualData
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (h logY : Nat -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n))
    (Hestimates : BankPaperCanonicalActualFrozenBaselineEstimates
      D fixed bankBase candidates preSelector activeSeed h logY) :
    BankPaperCanonicalFrozenBaselineSourceLedger
      h logY
      (bankPaperCanonicalActualFrozenLogMassFamily
        D fixed bankBase candidates preSelector activeSeed)
      (bankPaperCanonicalActualFrozenTotalMassFamily
        D fixed bankBase candidates preSelector activeSeed)
      (bankPaperCanonicalLiteralQMass D activeSeed) := by
  refine ⟨?_, Hestimates.2.1, Hestimates.2.2⟩
  apply Hestimates.1.congr'
  · filter_upwards [Hconstructor] with n hn
    unfold bankPaperCanonicalActualFrozenTotalMassFamily
      bankPaperCanonicalLiteralQMass
    rw [bankPaperCanonicalActualFrozenTotalMass_add_literalActiveMass_eq
      (D n) (T n) (fixed n) (bankBase n) (candidates n) (preSelector n)
        (activeSeed n) hn]
  · exact EventuallyEq.rfl

/-- Final literal tail-family connector.  It produces the old analytic
ledger for the actual tagged active mass and the actual frozen logarithmic
data, using the honest total guarded-base extension on the finite prefix. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_actualData
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (mFrozen h logY : Nat -> Real)
    (Hsource : BankPaperCanonicalSectionEightActualDataSourceLedger
      D T fixed bankBase candidates preSelector activeSeed
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      h logY) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      (bankPaperCanonicalLiteralQMass D activeSeed)
      (bankPaperCanonicalSmoothA0Family
        logY
        (bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector activeSeed)
        mFrozen (bankPaperCanonicalLiteralQMass D activeSeed)) := by
  apply bankPaperCanonicalSectionEightAnalyticLedger_of_correctionAndBaseline
    depth W K betaAct deltaStar F
    (bankPaperCanonicalLiteralQMass D activeSeed) h logY
    (bankPaperCanonicalActualFrozenLogMassFamily
      D fixed bankBase candidates preSelector activeSeed)
    (bankPaperCanonicalActualFrozenTotalMassFamily
      D fixed bankBase candidates preSelector activeSeed)
    mFrozen
  · exact bankPaperCanonicalGuardedSmoothCorrectionEstimate_of_actualData
      D activeSeed
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
        Hsource.2.1
  · exact bankPaperCanonicalFrozenBaselineSourceLedger_of_actualData
      D T fixed bankBase candidates preSelector activeSeed h logY
        Hsource.1 Hsource.2.2

/-- Canonical scaled-seed specialization.  Here `qTilde` is the literal
guarded-base mass itself, because the constructed seed has exactly that
mass; no postulated active-mass comparison remains. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (mFrozen h logY : Nat -> Real)
    (Hsource : BankPaperCanonicalSectionEightScaledActualDataSourceLedger
      D T fixed bankBase candidates preSelector
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      h logY) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      (bankPaperCanonicalSmoothA0Family
        logY
        (bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector
            (fun n => bankPaperCanonicalScaledActiveSeed (T n)
              (F.extendedGuardedSmoothBaseMass
                W K betaAct deltaStar n)))
        mFrozen
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)) := by
  have Hactual : BankPaperCanonicalSectionEightActualDataSourceLedger
      D T fixed bankBase candidates preSelector
      (fun n => bankPaperCanonicalScaledActiveSeed (T n)
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar n))
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      h logY :=
    ⟨Hsource.1,
      bankPaperCanonicalActualGuardedSmoothMassEstimate_scaledActiveSeed
        D T (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar),
      Hsource.2⟩
  have hqMass :
      bankPaperCanonicalLiteralQMass D
          (fun n => bankPaperCanonicalScaledActiveSeed (T n)
            (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar n)) =
        F.extendedGuardedSmoothBaseMass W K betaAct deltaStar := by
    funext n
    simp only [bankPaperCanonicalLiteralQMass,
      bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]
  have hledger :=
    bankPaperCanonicalSectionEightAnalyticLedger_of_actualData
      depth W K betaAct deltaStar F D T fixed bankBase candidates
        preSelector
        (fun n => bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar n))
        mFrozen h logY Hactual
  rw [hqMass] at hledger
  exact hledger

/-- Generic paper-facing central-tail adapter with an explicit selector-mass
interface.  See the following theorem for its construction from the
rough-stage baseline ledger. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData_intervalGeometry
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} {N : Nat} (hc : 0 < c) (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (mFrozen : Nat -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n)
          (bankPaperCanonicalScaledActiveSeed (T n)
            (F.extendedGuardedSmoothBaseMass
              W K betaAct deltaStar n)))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates)
    (Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates preSelector) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      (bankPaperCanonicalSmoothA0Family
        (bankPaperCanonicalCentralTailLogTarget c)
        (bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector
            (fun n => bankPaperCanonicalScaledActiveSeed (T n)
              (F.extendedGuardedSmoothBaseMass
                W K betaAct deltaStar n)))
        mFrozen
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)) := by
  apply bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData
    depth W K betaAct deltaStar F D T fixed bankBase candidates
      preSelector mFrozen (bankPaperCanonicalUpperTailHeight c)
        (bankPaperCanonicalCentralTailLogTarget c)
  exact
    bankPaperCanonicalSectionEightScaledActualDataSourceLedger_of_intervalGeometry
      hc D T fixed bankBase candidates preSelector
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
        Hconstructor Hgeometry Hselector





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightPrechargedLogConnector -/
section


/-!
# Paper-faithful precharged logarithmic target for Section 8

Section 8 removes the guarded central-anchor divisor before it forms the
ordinary-log target used by the smooth height ledger.  Thus the literal
quantity called `log Y` in the paper is

`log (centralTailProduct / centralAnchorDivisor)`,

not the logarithm of the complete central tail.  This file gives that
certificate-dependent target a total extension on an honest guarded tail
family.  On the finite prefix the extension agrees with the complete-tail
logarithm and the anchor log is zero; this convention changes no asymptotic
statement and makes their exact additive identity valid at every index.

The anchor logarithm is `O(secondOrderScale)` without any new analytic
assumption.  Its factorization has fixed support
`primesUpTo (2 * depth + 1)`, and exact divisibility bounds each supported
valuation by the corresponding upper-tail valuation.  The existing
fixed-prime valuation asymptotic then supplies the required finite sum
bound.  Subtracting this anchor log transfers both the centered complete-tail
estimate and any already-constructed Section 8 analytic ledger to the
paper's precharged logarithmic target.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperCanonicalGuardedTailFamily





/-- On a genuine tail fiber, the total precharged target is the literal
certificate-dependent quotient target. -/
theorem extendedPrechargedTailLogTarget_eq
    {c : Real} {depth N n : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hn : N <= n) :
    F.extendedPrechargedTailLogTarget n =
      Real.log ((F.certificate n hn).prechargedTailTarget : Real) := by
  rw [extendedPrechargedTailLogTarget, dif_pos hn]

/-- On a genuine tail fiber, the total anchor log is the literal guarded
central-anchor-divisor log. -/
theorem extendedCentralAnchorDivisorLog_eq
    {c : Real} {depth N n : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hn : N <= n) :
    F.extendedCentralAnchorDivisorLog n =
      Real.log
        (centralAnchorDivisor n (centralAnchorCutoff depth n)
          (F.certificate n hn).q : Real) := by
  rw [extendedCentralAnchorDivisorLog, dif_pos hn]

/-- Exact paper identity on every genuine tail fiber:
`log Y + log D' = log T`. -/
theorem extendedPrechargedTailLogTarget_add_anchorLog_of_tail
    {c : Real} {depth N n : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hn : N <= n) :
    F.extendedPrechargedTailLogTarget n +
        F.extendedCentralAnchorDivisorLog n =
      bankPaperCanonicalCentralTailLogTarget c n := by
  let certificate := F.certificate n hn
  let divisor :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  have htarget : certificate.prechargedTailTarget * divisor =
      centralTailProduct n (upperTailLength c n) := by
    simpa only [divisor] using
      certificate.prechargedTailTarget_mul_centralAnchorDivisor
  have htargetNe : (certificate.prechargedTailTarget : Real) ≠ 0 := by
    exact_mod_cast certificate.prechargedTailTarget_pos.ne'
  have hdivisorNe : (divisor : Real) ≠ 0 := by
    exact_mod_cast
      (centralAnchorDivisor_pos certificate.isCofactorChoice).ne'
  rw [extendedPrechargedTailLogTarget_eq F hn,
    extendedCentralAnchorDivisorLog_eq F hn,
    bankPaperCanonicalCentralTailLogTarget]
  change
    Real.log (certificate.prechargedTailTarget : Real) +
        Real.log (divisor : Real) =
      Real.log (centralTailProduct n (upperTailLength c n) : Real)
  rw [← Real.log_mul htargetNe hdivisorNe, ← Nat.cast_mul, htarget]

/-- The complementary finite-prefix conventions make the same exact
identity valid at every natural-number index. -/
theorem extendedPrechargedTailLogTarget_add_extendedCentralAnchorDivisorLog
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (n : Nat) :
    F.extendedPrechargedTailLogTarget n +
        F.extendedCentralAnchorDivisorLog n =
      bankPaperCanonicalCentralTailLogTarget c n := by
  by_cases hn : N <= n
  · exact F.extendedPrechargedTailLogTarget_add_anchorLog_of_tail hn
  · simp only [extendedPrechargedTailLogTarget,
      extendedCentralAnchorDivisorLog, dif_neg hn, add_zero]

end BankPaperCanonicalGuardedTailFamily

namespace GuardedCentralAnchorCertificate

/-- Exact divisibility bounds every guarded anchor valuation by the
corresponding literal upper-tail valuation. -/
theorem centralAnchorDivisor_factorization_le_upperTailValuation
    {c : Real} {depth n p : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    ((centralAnchorDivisor n (centralAnchorCutoff depth n)
        certificate.q).factorization p : Real) <=
      (upperTailValuation c n p : Real) := by
  have hdivisorPos :
      0 < centralAnchorDivisor n (centralAnchorCutoff depth n)
        certificate.q :=
    centralAnchorDivisor_pos certificate.isCofactorChoice
  have htailPos :
      0 < centralTailProduct n (upperTailLength c n) :=
    centralTailProduct_pos n (upperTailLength c n)
  have hfactorization :
      (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q).factorization p <=
        (centralTailProduct n
          (upperTailLength c n)).factorization p :=
    ((Nat.factorization_le_iff_dvd hdivisorPos.ne' htailPos.ne').mpr
      certificate.divisor_dvd_tail) p
  rw [upperTailValuation_eq_centralTailProduct_factorization]
  exact_mod_cast hfactorization

/-- Fixed-support expansion of the guarded anchor-divisor logarithm. -/
theorem centralAnchorDivisorLog_eq_sum_primesUpTo
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    Real.log
        (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q : Real) =
      ∑ p ∈ primesUpTo (2 * depth + 1),
        ((centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q).factorization p : Real) *
          Real.log (p : Real) := by
  classical
  let divisor :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  have hdivisorPos : 0 < divisor := by
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  rw [Real.log_nat_eq_sum_factorization]
  change
    (∑ p ∈ divisor.factorization.support,
        (divisor.factorization p : Real) * Real.log (p : Real)) =
      ∑ p ∈ primesUpTo (2 * depth + 1),
        (divisor.factorization p : Real) * Real.log (p : Real)
  apply Finset.sum_subset
  · intro p hpSupport
    have hpNonzero : divisor.factorization p ≠ 0 :=
      Finsupp.mem_support_iff.mp hpSupport
    have hpPrime : p.Prime :=
      Not.imp_symm divisor.factorization_eq_zero_of_not_prime hpNonzero
    have hpDvd : p ∣ divisor := by
      apply (hpPrime.dvd_iff_one_le_factorization hdivisorPos.ne').mpr
      exact Nat.one_le_iff_ne_zero.mpr hpNonzero
    exact certificate.divisor_prime_support p hpPrime
      (by simpa only [divisor] using hpDvd)
  · intro p _hpPrefix hpNotSupport
    have hpZero : divisor.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp hpNotSupport
    simp only [hpZero, Nat.cast_zero, zero_mul]

end GuardedCentralAnchorCertificate

/-! ## The fixed-prime asymptotic bound -/

/-- The fixed-prime valuation limits give one simultaneous upper bound on
the complete anchor support. -/
theorem eventually_upperTailValuation_le_add_one_mul_secondOrderScale_on_primesUpTo
    {c : Real} (hc : 0 < c) (depth : Nat) :
    ∀ᶠ n : Nat in atTop, ∀ p ∈ primesUpTo (2 * depth + 1),
      (upperTailValuation c n p : Real) <=
        (c / ((p - 1 : Nat) : Real) + 1) *
          secondOrderScale n := by
  have hratio :
      ∀ᶠ n : Nat in atTop, ∀ p ∈ primesUpTo (2 * depth + 1),
        (upperTailValuation c n p : Real) / secondOrderScale n <=
          c / ((p - 1 : Nat) : Real) + 1 := by
    rw [Finset.eventually_all]
    intro p hp
    have hpPrime : p.Prime := (mem_primesUpTo.mp hp).1
    exact
      (upperTailValuation_normalized_tendsto hc hpPrime).eventually
        (eventually_le_nhds (by linarith))
  filter_upwards [hratio, eventually_secondOrderScale_pos] with
      n hn hscale
  intro p hp
  exact (div_le_iff₀ hscale).mp (hn p hp)





namespace BankPaperCanonicalGuardedTailFamily

/-- Uniformly over every coherent guarded tail family, the removed
central-anchor logarithm is `O(n / log n)`.  The proof uses fixed prime
support and fixed-prime valuation asymptotics, rather than the much too
coarse numerical inequality `divisor <= tail`. -/
theorem extendedCentralAnchorDivisorLog_isBigO_secondOrderScale
    {c : Real} {depth N : Nat} (hc : 0 < c)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    F.extendedCentralAnchorDivisorLog =O[atTop] secondOrderScale := by
  apply IsBigO.of_bound (bankPaperCanonicalAnchorLogBigOConstant c depth)
  filter_upwards [eventually_ge_atTop N,
      eventually_upperTailValuation_le_add_one_mul_secondOrderScale_on_primesUpTo
        hc depth,
      eventually_secondOrderScale_pos] with n hnTail hvaluation hscale
  let certificate := F.certificate n hnTail
  let divisor :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  have hdivisorPos : 0 < divisor := by
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  have hlogNonneg : 0 <= Real.log (divisor : Real) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hdivisorPos.ne'
  rw [extendedCentralAnchorDivisorLog_eq F hnTail,
    Real.norm_eq_abs, abs_of_nonneg hlogNonneg,
    Real.norm_eq_abs, abs_of_pos hscale,
    certificate.centralAnchorDivisorLog_eq_sum_primesUpTo]
  calc
    (∑ p ∈ primesUpTo (2 * depth + 1),
        (divisor.factorization p : Real) * Real.log (p : Real)) <=
      ∑ p ∈ primesUpTo (2 * depth + 1),
        ((c / ((p - 1 : Nat) : Real) + 1) * secondOrderScale n) *
          Real.log (p : Real) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPrime : p.Prime := (mem_primesUpTo.mp hp).1
        have hpLogNonneg : 0 <= Real.log (p : Real) :=
          Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
        apply mul_le_mul_of_nonneg_right _ hpLogNonneg
        exact
          (certificate.centralAnchorDivisor_factorization_le_upperTailValuation
            (p := p)).trans (hvaluation p hp)
    _ = ∑ p ∈ primesUpTo (2 * depth + 1),
        ((c / ((p - 1 : Nat) : Real) + 1) *
          Real.log (p : Real)) * secondOrderScale n := by
        apply Finset.sum_congr rfl
        intro p _hp
        ring
    _ = bankPaperCanonicalAnchorLogBigOConstant c depth *
          secondOrderScale n := by
        rw [bankPaperCanonicalAnchorLogBigOConstant, Finset.sum_mul]



end BankPaperCanonicalGuardedTailFamily

/-! ## Adapter for an already-constructed Section 8 ledger -/

/-- Replace the old complete-central-tail logarithm in an existing Section 8
analytic ledger by the paper's precharged logarithm.  The active-mass field
is unchanged; the height defect changes by exactly the anchor-divisor log,
which is already `O(secondOrderScale)`. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_precharged_of_centralTail
    {c : Real} {depth N : Nat} (hc : 0 < c)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (rawBase qTilde Lambda0 mFrozen : Nat -> Real)
    (Hcentral : BankPaperCanonicalSectionEightAnalyticLedger
      rawBase qTilde
      (bankPaperCanonicalSmoothA0Family
        (bankPaperCanonicalCentralTailLogTarget c)
        Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalSectionEightAnalyticLedger
      rawBase qTilde
      (bankPaperCanonicalSmoothA0Family
        F.extendedPrechargedTailLogTarget
        Lambda0 mFrozen qTilde) := by
  constructor
  · exact Hcentral.1
  · have hanchor :=
      F.extendedCentralAnchorDivisorLog_isBigO_secondOrderScale hc
    have hheight := Hcentral.2.sub hanchor
    exact hheight.congr_left fun n => by
      unfold bankPaperCanonicalSmoothA0Family
      unfold bankPaperCanonicalSmoothFrozenHeightDefect
      rw [← F.extendedPrechargedTailLogTarget_add_extendedCentralAnchorDivisorLog
        n]
      ring

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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGlobalCorrectedSourceSelector -/
section


/-!
# Global corrected source selector

The original two-zero-cell source selector uses the protected-plus-active
weight on the smooth guarded broad pool and the old active ambient weight
everywhere else.  That is the right source for the Section 8 moment ledger,
but it is not the selector required by the Section 9 endpoint theorem on a
nonsmooth active row.

This file makes a rowwise compatible global replacement.  Off the smooth
broad pool it keeps the old ambient weight on complete-rough label `1`, and
uses the already constructed postcharge corrected row weight on active
nonexceptional labels, while exceptional labels are zero.  Consequently:

* once structured active values are known to lie in the complete smooth
  row, the source still agrees with the old ambient weight at every such
  coordinate outside the smooth broad pool, so the existing two-zero-cell
  prebridge ledger applies unchanged;
* every active nonsmooth guarded broad coordinate is exactly the explicit
  postcharge corrected row weight; and
* after structured placement, the two exact `hpreNonsmooth` and
  `hpreUpper` interfaces consumed by the endpoint-slack theorem are exposed.

The exact corrected-weight identity uses the literal active-nonexceptional
classification; preservation by structured placement additionally uses
smooth-row support of the structured active values.  The smooth upper theorem
honestly retains the pointwise `O(1 / L)` upper bound for the placement seed.
Existing two-zero-cell capacity only bounds the resulting selector by `1`;
it does not imply this sharper estimate.

On an active nonexceptional complete label, the outside selector intentionally
uses the full corrected-row weight, including its raw-weight branch outside
the guarded broad correction pool.  This is the rowwise selector whose total
is controlled by the postcharge construction, rather than a pointwise-only
patch of the old ambient source.  A rounded-selector input for this global
source remains explicit below; it is not manufactured from local slack.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Arbitrary-seed push-forward -/

/-- Numerical head-pattern separation makes the structured value map
injective, so the ambient push-forward of an arbitrary seed at an occupied
coordinate is exactly the corresponding tagged weight.  This elementary
form is kept below the Section 8 one-shot layer so that the latter can reuse
the global source connector without an import cycle. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (hsep : D.HeadPatternsSeparated) (m : D.Sample) :
    bankPaperCanonicalActiveSeedAmbientWeight D seed (D.value m) =
      seed m := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  rw [Finset.sum_eq_single m]
  · simp
  · intro k _hk hkm
    rw [if_neg]
    intro hvalue
    exact hkm (D.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

/-! ## The global outside selector -/









/-! ## The global source and its exact rowwise values -/







/-! ## Compatibility with the Section 8 prebridge ledger -/



/-! ## Full Section 8 placement with the global source -/







/-! ## Exact endpoint-slack inputs after structured placement -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTopFrozenSourceConnector -/
section


/-!
# The frozen smooth-top source at the Section 8 initial stage

The paper's smooth-row initialization has three distinct layers:

* the `alpha`-weighted top block;
* the protected `betaProt / L` broad layer; and
* the structured active seed of total mass `qTilde`.

The older global corrected source retained the latter two layers on the
guarded broad pool, but its complete-label-one branch contained only the
ambient active seed.  In particular it did not contain the top block.

This connector defines a separate, finite `qTilde`-stage source which adds
that missing top layer.  On the guarded complete smooth row it is pointwise
equal to the literal raw weight with broad parameter `betaProt`, plus the
ambient old seed.  Consequently, when the old seed has total mass equal to
the guarded `betaAct` base mass, its whole guarded smooth-row sum is exactly
the balanced raw sum with broad parameter `betaProt + betaAct`.

No asymptotic estimate, post-height-fit displacement, or Section 9 source
state is asserted here.  The identities are finite and exact.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The missing smooth top layer -/







/-! ## Pointwise smooth-row identification -/





/-! ## Exact guarded-row mass identities -/

/-- Summing the pointwise bridge identifies the restored source mass with
the frozen raw mass plus the literal total mass of the old seed. -/
theorem sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_frozenRaw_add_activeMass
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a) =
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed := by
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
          (K := K) B R certificate oldSeed ha
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed := by
      rw [sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
        B.sampleData oldSeed
          (R.roughCanonicalGuardedRow certificate deltaStar K 1)
            hvalues]

/-- Pointwise splitting of the broad coefficient on the guarded smooth row.
The active summand is supported exactly on the guarded head-free broad pool. -/
theorem roughHeadCompatibleRawWeight_split_protected_active_of_mem_guardedSmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt betaAct alpha : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha
          (betaProt + betaAct) B.L a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
        if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1 then
          betaAct / B.L
        else 0 := by
  by_cases hpool :
      a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1
  · have hbroad :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
        certificate deltaStar B.sampleData.W K 1 hpool
    rw [roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
        (alpha := alpha) (beta := betaProt + betaAct) (L := B.L) hbroad,
      roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
        (alpha := alpha) (beta := betaProt) (L := B.L) hbroad,
      if_pos hpool]
    ring
  · have hprot :=
      bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
        (B := B) R certificate (alpha := alpha) (beta := betaProt)
          ha hpool
    have htotal :=
      bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
        (B := B) R certificate (alpha := alpha)
          (beta := betaProt + betaAct) ha hpool
    rw [if_neg hpool, add_zero]
    exact htotal.symm.trans hprot

/-- The raw broad-parameter split summed over the guarded smooth row. -/
theorem sum_roughHeadCompatibleRawWeight_split_protected_active_guardedSmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt betaAct alpha : Real) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha
          (betaProt + betaAct) B.L a) =
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
          B.sampleData.W K betaAct := by
  have hfilter :
      (R.roughCanonicalGuardedRow certificate deltaStar K 1).filter
          (fun a =>
            a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1) =
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · exact fun ha => ha.2
    · intro ha
      exact
        ⟨R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
            certificate deltaStar B.sampleData.W K 1 ha,
          ha⟩
  have hactiveSum :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1 then
          betaAct / B.L
        else 0) =
      betaAct / B.L *
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1).card : Real) := by
    rw [← Finset.sum_filter, hfilter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha
          (betaProt + betaAct) B.L a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
            if a ∈
                R.roughCanonicalGuardedBroadCorrectionPool certificate
                  deltaStar B.sampleData.W K 1 then
              betaAct / B.L
            else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact
        roughHeadCompatibleRawWeight_split_protected_active_of_mem_guardedSmoothRow
          (K := K) B R certificate ha
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1 then
            betaAct / B.L
          else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        betaAct / B.L *
          ((R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1).card : Real) := by
      rw [hactiveSum]
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
          B.sampleData.W K betaAct := by
      simp only [bankPaperCanonicalGuardedSmoothBaseMass,
        BridgeData.L, Erdos390.Full.Scale.L]

/-- Exact `xTop + fProt + oldSeed = balanced raw` guarded-row ledger.
The only identification premise is the paper's literal statement that the
old seed mass is the guarded active base mass. -/
theorem sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_balancedRaw
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt betaAct alpha : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hmass :
      bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed =
        bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
          B.sampleData.W K betaAct) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha
          (betaProt + betaAct) oldSeed a) =
      ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha
            (betaProt + betaAct) B.L a := by
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha
          (betaProt + betaAct) oldSeed a) =
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
          bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed :=
      sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_frozenRaw_add_activeMass
        (K := K) B R certificate oldSeed hvalues
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
          B.sampleData.W K betaAct := by
      rw [hmass]
    _ = ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha
            (betaProt + betaAct) B.L a := by
      symm
      exact
        sum_roughHeadCompatibleRawWeight_split_protected_active_guardedSmoothRow
          (K := K) B R certificate deltaStar betaProt betaAct alpha

/-- Scaled-seed specialization.  The normalization theorem reduces the
mass premise to the displayed equality `q = guardedSmoothBaseMass`. -/
theorem sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_scaledSeed_smoothRow_eq_balancedRaw
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct alpha q : Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hq :
      q = bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
        B.sampleData.W K betaAct) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha
          (betaProt + betaAct)
            (bankPaperCanonicalScaledActiveSeed T q) a) =
      ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha
            (betaProt + betaAct) B.L a := by
  apply
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_balancedRaw
      (K := K) B R certificate deltaStar betaProt betaAct alpha
        (bankPaperCanonicalScaledActiveSeed T q) hvalues
  simpa only [bankPaperCanonicalLiteralActiveMass_scaledActiveSeed] using hq

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





/-! ## Full label-one guard deletion -/









/-! ## Paper-scale bounds for the smooth row -/











/-! ## Exact construction boundary and the charged mass ledger -/





/-! ## Asymptotic initial-selector mass theorem -/



/-! ## The concrete WithTop/scaled-seed constructor -/

/-- The exact scaled-seed smooth-row theorem from the frozen-top source
constructs the finite witness required above, provided the same selector
already carries the charged nonsmooth rows.

This deliberately remains a finite constructor: turning an arbitrary
family of `BridgeData` into a family indexed definitionally by its sample
integer requires a separate synchronization interface. -/
theorem bankPaperCanonicalTopFrozenBalancedInitialRealization_of_scaledSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct q : Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (hq :
      q = bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
        B.sampleData.W (K0 + 1) betaAct)
    (hrows :
      BankPaperCanonicalChargedNonsmoothRowRealization
        (K := K0 + 1) R certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
            (K := K0 + 1) B R certificate deltaStar betaProt
              (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
                (upperTailLength c B.sampleData.n) (K0 + 1)
                  (betaProt + betaAct) B.L)
              (betaProt + betaAct)
              (bankPaperCanonicalScaledActiveSeed T q))) :
    BankPaperCanonicalTopFrozenBalancedInitialRealization
      depth B.sampleData.W K0 B.sampleData.n c deltaStar
        (betaProt + betaAct)
        (R.paperFixedExceptionalFactors deltaStar)
        R.prechargeBaseState
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar
          (K0 + 1))
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
          (K := K0 + 1) B R certificate deltaStar betaProt
            (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) (K0 + 1)
                (betaProt + betaAct) B.L)
            (betaProt + betaAct)
            (bankPaperCanonicalScaledActiveSeed T q)) := by
  refine ⟨R, certificate, rfl, rfl, rfl, hrows, ?_⟩
  simpa only [bankPaperCanonicalBalancedRawWeight,
    BridgeData.L, Scale.L] using
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_scaledSeed_smoothRow_eq_balancedRaw
      (K := K0 + 1) B R certificate T deltaStar betaProt betaAct
        (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) (K0 + 1)
            (betaProt + betaAct) B.L)
        q hvalues hq

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateConnector -/
section


/-!
# Nearest-integer source state for the frozen-top selector

The finite frozen-top source at mass `qTilde` has the paper's literal
smooth-row mass, but that mass need not be an integer.  The initialization
step replaces `qTilde` by

`q0 = nearestInteger(mFrozen + qTilde) - mFrozen`.

This connector proves the exact part of that handoff:

* changing the scaled seed from `qTilde` to `q0` changes no nonsmooth row;
* the new smooth-row total is the declared nearest integer;
* the charged nonsmooth-row equations therefore imply integrality of every
  complete rough row; and
* feasibility and exact target agreement outside the tangent prime band
  then package the result as `BankPaperCanonicalSelectorSourceState`.

The last two properties are retained as explicit premises.  They are not
consequences of row-mass rounding: feasibility is pointwise, while target
agreement is a prime-valuation identity.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The exact frozen mass and nearest-integer source -/













/-! ## Nonsmooth rows are independent of the active seed -/

/-- On every nonsmooth guarded row, changing the structured active seed is
pointwise invisible.  Active nonexceptional rows use the same corrected
weight for both seeds, while exceptional rows are zero for both seeds. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_eq_of_mem_nonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha betaTotal : Real)
    (oldSeed₁ oldSeed₂ : B.sampleData.Sample -> Real) {a : Nat}
    (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed₁ a =
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed₂ a := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hlabel (haLabel.symm.trans haSmoothLabel)
  simp only [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
    bankPaperCanonicalTwoZeroHeadCellSourceSelector, hnotSmoothPool,
    if_false, bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
    haLabel, hlabel]





/-- Replacing `qTilde` by `q0` is pointwise invisible on every nonsmooth
guarded row. -/
theorem bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    {a : Nat} (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde a =
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
  unfold bankPaperCanonicalTopFrozenRoundedSourceSelector
  exact
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_eq_of_mem_nonsmoothRow
      (K := K) B R certificate deltaStar betaProt alpha betaTotal
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        (bankPaperCanonicalScaledActiveSeed T qTilde) hlabel ha

/-! ## Exact smooth and nonsmooth row ledgers -/











/-! ## Exact feasibility transport through the two zero cells -/



/-! ## Complete-row integrality and the source-state handoff -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateEventualConnector -/
section


/-!
# Eventual construction of the frozen-top rounded source state

The finite nearest-integer connector reduces the frozen-top source state to
three kinds of input:

* canonical sample geometry and the capacities of the two zero-head cells;
* feasibility of the literal `qTilde` source and its charged nonsmooth rows;
* exact selector-tail agreement outside the medium-prime band.

The first group is already asymptotic.  Canonical sample geometry is
provided by
`bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs`.  The
generic two-cell scalar-capacity theorem also supplies the initialization
capacity once it is applied to the uniformly bounded change
`(q0 - qTilde) / 2`.

This file packages that reuse.  The remaining residual input records only
the three facts for which the repository has no source-specific producer:
literal `qTilde` feasibility, charged nonsmooth rows, and literal `qTilde`
selector-tail support.  The zero-head correction is proved below to preserve
that support.  The equality identifying the analytic family `mFrozen` with
the concrete frozen-top row mass is also kept explicit at the eventual
synchronization boundary.
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

/-! ## The initial-only cell change and its capacity -/







/-! ## Selector-tail support transport -/

/-- On the guarded candidate set, replacing `qTilde` by the nearest-integer
seed changes the frozen-top source by exactly the corresponding ambient seed
change.  On the smooth row the frozen raw layer cancels; on every nonsmooth
row both sources agree and both active ambient weights vanish. -/
theorem
    bankPaperCanonicalTopFrozenRoundedSourceSelector_sub_qTildeSource_eq_ambient_sub
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {a : Nat}
    (ha : a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K) :
    bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a -
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde) a -
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have haSmooth :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, hlabel⟩)
    rw [bankPaperCanonicalTopFrozenRoundedSourceSelector,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde)
          haSmooth,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate (bankPaperCanonicalScaledActiveSeed T qTilde)
          haSmooth]
    ring
  · have haRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K
          (completeRoughLabel (yNat B.sampleData.n) a) := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩)
    have hsourceEq :=
      bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal
          qTilde hlabel haRow
    have hnewZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      have hmLabel := (mem_completeRoughRowFiber.mp hmSmooth).2
      exact hlabel hmLabel
    have holdZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      have hmLabel := (mem_completeRoughRowFiber.mp hmSmooth).2
      exact hlabel hmLabel
    rw [hsourceEq, hnewZero, holdZero]
    ring







/-! ## Exact residual input -/



/-! ## Finite assembly -/



/-! ## Eventual canonical supplier -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstActualData -/
section


/-!
# Source-first actual-data identities

This module supplies the two finite facts needed to build the exact Section 8
ledger before the post-height bridge.

* The pre-rounding global corrected source selector, paired with the genuine
  barycentric scaled seed, satisfies the actual active-measure constructor.
* Floating rounding changes the selector and its ambient seed by exactly the
  same pointwise amount.  Hence their frozen remainder, and therefore its
  literal logarithmic mass, is unchanged.

These are exact finite statements.  They contain no asymptotic estimate or
ledger hypothesis.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The pre-rounding actual active measure -/

/-- The source-first corrected selector paired with the literal scaled
barycentric seed is an honest actual active-measure constructor. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_actualActiveMeasureConstructor
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hqTilde : 1 ≤ qTilde)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hbetaProtBox :
      0 ≤ betaProt / B.L ∧ betaProt / B.L ≤ 1)
    (hselectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 ≤
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde))
      (bankPaperCanonicalScaledActiveSeed T qTilde) := by
  apply bankPaperCanonicalActualActiveMeasureConstructor_of_coordinateFit
    B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde))
      qTilde hqTilde hsep
  · intro m
    exact
      (mem_completeRoughRowFiber.mp
        (hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr
            ⟨m, rfl⟩))).1
  · exact hselectorNonneg
  · unfold BankPaperCanonicalActualCoordinateFit
    intro m
    have hmSmooth :
        B.sampleData.value m ∈
          R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      hactiveSmooth
        (mem_bankPaperCanonicalStructuredActiveValues.mpr
          ⟨m, rfl⟩)
    rw [
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        (K := K) B R certificate
          (bankPaperCanonicalScaledActiveSeed T qTilde) hmSmooth,
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
        B.sampleData (bankPaperCanonicalScaledActiveSeed T qTilde)
          hsep m]
    exact le_add_of_nonneg_left
      (roughHeadCompatibleRawWeight_mem_unitInterval
        (W := B.sampleData.W) (n := B.sampleData.n)
        (h := upperTailLength c B.sampleData.n) (K := K)
        (α := alpha) (β := betaProt) (L := B.L)
        halpha hbetaProtBox (B.sampleData.value m)).1

/-! ## Exact frozen-log invariance under floating rounding -/

/-- The rounded source pair and the pre-rounding scaled source pair have
exactly the same literal frozen logarithmic mass. -/
theorem
    bankPaperCanonicalTopFrozenRounded_actualFrozenLogMass_eq_qTildeSource
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed bankBase : Finset Nat)
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    bankPaperCanonicalActualFrozenLogMass B.sampleData fixed bankBase
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde)
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde) =
      bankPaperCanonicalActualFrozenLogMass B.sampleData fixed bankBase
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde))
        (bankPaperCanonicalScaledActiveSeed T qTilde) := by
  classical
  have hcandidate :
      (∑ a : BankPaperCanonicalActualFrozenIndex
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K),
        bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K)
            (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate T deltaStar betaProt alpha betaTotal
                qTilde)
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a *
          Real.log
            (bankPaperCanonicalActualFrozenValue a : Real)) =
        ∑ a : BankPaperCanonicalActualFrozenIndex
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K),
        bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K)
            (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
              (K := K) B R certificate deltaStar betaProt alpha
                betaTotal
                (bankPaperCanonicalScaledActiveSeed T qTilde))
            (bankPaperCanonicalScaledActiveSeed T qTilde) a *
          Real.log
            (bankPaperCanonicalActualFrozenValue a : Real) := by
    apply Finset.sum_congr rfl
    intro a _ha
    have hdiff :=
      bankPaperCanonicalTopFrozenRoundedSourceSelector_sub_qTildeSource_eq_ambient_sub
        (K := K) B R certificate T deltaStar betaProt alpha
          betaTotal qTilde hactiveSmooth a.2
    have hweight :
        bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K)
            (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate T deltaStar betaProt alpha betaTotal
                qTilde)
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a =
          bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K)
            (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
              (K := K) B R certificate deltaStar betaProt alpha
                betaTotal
                (bankPaperCanonicalScaledActiveSeed T qTilde))
            (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
      unfold bankPaperCanonicalActualFrozenWeight
      linarith only [hdiff]
    rw [hweight]
  unfold bankPaperCanonicalActualFrozenLogMass
  rw [hcandidate]

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstLedgerConnector -/
section


/-!
# Exact source-first Section 8 ledger

This connector constructs the analytic ledger from an honest family of
pre-rounding scaled source data.  Its hypotheses are only:

* the finite actual active-measure constructor;
* the literal interval geometry;
* and the finite top-frozen balanced initial realization.

The selector-mass estimate is proved by the existing balanced-row theorem,
the central-tail ledger is proved by the actual-data connector, and the
logarithmic target is then replaced by the exact precharged target.  The
literal frozen logarithmic family remains visible in the conclusion.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

/-- Build the exact precharged Section 8 ledger from the source-first
pre-rounding actual-data family. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_sourceFirstAnalyticLedger_of_actualData
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c betaAct deltaStar betaTotal : Real} {N : Nat}
    (hc : 0 < c) (hdeltaStar : 0 < deltaStar)
    (hdeltaStarUpper : deltaStar < 1)
    (depth W K0 poolMinimum : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (D : Nat → StructuredSampleData Head)
    (T : ∀ n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat → Finset Nat)
    (preSelector : Nat → Nat → Real)
    (mFrozen : Nat → Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n)
        (bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n)))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates)
    (Hbalanced : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalTopFrozenBalancedInitialRealization
        depth W K0 n c deltaStar betaTotal
          (fixed n) (bankBase n) (candidates n)
          (preSelector n)) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) (K0 + 1) betaAct)
      (F.extendedGuardedSmoothBaseMass
        W (K0 + 1) betaAct deltaStar)
      (bankPaperCanonicalSmoothA0Family
        F.extendedPrechargedTailLogTarget
        (bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector
          (fun n => bankPaperCanonicalScaledActiveSeed (T n)
            (F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n)))
        mFrozen
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)) := by
  have Hselector :
      BankPaperCanonicalActualSelectorMassEstimate
        c fixed bankBase candidates preSelector :=
    bankPaperCanonicalActualSelectorMassEstimate_of_topFrozenBalancedInitial
      depth W K0 poolMinimum hc hdeltaStar hdeltaStarUpper
        fixed bankBase candidates preSelector Hbalanced
  have Hcentral :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          (bankPaperCanonicalCentralTailLogTarget c)
          (bankPaperCanonicalActualFrozenLogMassFamily
            D fixed bankBase candidates preSelector
            (fun n => bankPaperCanonicalScaledActiveSeed (T n)
              (F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n)))
          mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar)) :=
    bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData_intervalGeometry
      hc depth W (K0 + 1) betaAct deltaStar F D T fixed bankBase
        candidates preSelector mFrozen Hconstructor Hgeometry Hselector
  exact
    bankPaperCanonicalSectionEightAnalyticLedger_precharged_of_centralTail
      hc F
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) (K0 + 1) betaAct)
      (F.extendedGuardedSmoothBaseMass
        W (K0 + 1) betaAct deltaStar)
      (bankPaperCanonicalActualFrozenLogMassFamily
        D fixed bankBase candidates preSelector
        (fun n => bankPaperCanonicalScaledActiveSeed (T n)
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n)))
      mFrozen Hcentral

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstLedgerFamilies -/
section


/-!
# Total source-first ledger families

The Section 8 ledger is a statement about whole natural-indexed families,
whereas the genuine bank, sample, and source target exist only on a tail.
This module performs the required dependent totalization honestly.

One complete dependent source fiber is reused on the finite prefix.  On the
tail, the supplied genuine fiber is used definitionally.  Every analytic
input is eventual, so the finite fallback has no mathematical effect.
The theorem then proves the actual-measure constructor, interval geometry,
and balanced initial realization from the literal source callback and feeds
them to the exact source-first ledger connector.
-/

open Filter Topology Set

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 800000 in
/-- A tail family of genuine source bridges yields total logarithmic and
frozen-mass families, the exact precharged Section 8 ledger, and pointwise
synchronization with the literal rounded source on the same tail.

The callback contains only finite source data and exact equalities.  It does
not contain an analytic ledger, a post-height bridge, or a final-mass
estimate. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstLedgerFamilies
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    {c deltaStar betaProt betaAct : Real}
    {depth N W K0 : Nat}
    (hc : 0 < c)
    (hdeltaStar : 0 < deltaStar)
    (hdeltaStarUpper : deltaStar < 1)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (source :
      ∀ n, N ≤ n →
        Σ B : BridgeData (PaperHeadSimplex.Tag P) Band,
          BankPaperCanonicalGuardedTailFiber
              c depth B.sampleData.n ×
            BarycentricTarget B.sampleData)
    (Hsource :
      ∀ᶠ n : Nat in atTop,
        ∀ hn : N ≤ n,
          let X := source n hn
          let B := X.1
          let R := X.2.1.1
          let certificate := X.2.1.2
          let T := X.2.2
          let alpha :=
            bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct
          let qTilde :=
            F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n
          B.sampleData.n = n ∧
            B.sampleData.W = W ∧
            qTilde =
              bankPaperCanonicalGuardedSmoothBaseMass
                R certificate deltaStar B.sampleData.W
                  (K0 + 1) betaAct ∧
            1 ≤ qTilde ∧
            B.sampleData.HeadPatternsSeparated ∧
            bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
              R.roughCanonicalGuardedRow
                certificate deltaStar (K0 + 1) 1 ∧
            (0 ≤ alpha ∧ alpha ≤ 1) ∧
            (0 ≤ betaProt / B.L ∧ betaProt / B.L ≤ 1) ∧
            BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
              (K := K0 + 1) B R certificate
              (R.paperFixedExceptionalFactors deltaStar)
              T deltaStar betaProt alpha
                (betaProt + betaAct) qTilde ∧
            certificate.prechargedTailTarget =
              (F.certificate n hn).prechargedTailTarget) :
    ∃ logY Lambda0 mFrozen : Nat → Real,
      logY = F.extendedPrechargedTailLogTarget ∧
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
            (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar)) ∧
      ∀ᶠ n : Nat in atTop,
        ∀ hn : N ≤ n,
          let X := source n hn
          let B := X.1
          let R := X.2.1.1
          let certificate := X.2.1.2
          let T := X.2.2
          let alpha :=
            bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct
          let qTilde :=
            F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n
          mFrozen n =
              bankPaperCanonicalTopFrozenSmoothFrozenMass
                (K := K0 + 1) B R certificate
                  deltaStar betaProt alpha ∧
            logY n =
              bankPaperCanonicalSectionNinePostHeightLogY
                B R certificate ∧
            Lambda0 n =
              bankPaperCanonicalSectionNinePostHeightRoundedLambda0
                (K0 + 1) B R certificate T
                  deltaStar betaProt alpha
                    (betaProt + betaAct) qTilde := by
  let X :
      Nat →
        Σ B : BridgeData (PaperHeadSimplex.Tag P) Band,
          BankPaperCanonicalGuardedTailFiber
              c depth B.sampleData.n ×
            BarycentricTarget B.sampleData :=
    fun n =>
      if hn : N ≤ n then
        source n hn
      else
        source N le_rfl
  have hX (n : Nat) (hn : N ≤ n) :
      X n = source n hn := by
    simp only [X, dif_pos hn]
  let B := fun n => (X n).1
  let R := fun n => (X n).2.1.1
  let certificate := fun n => (X n).2.1.2
  let D : Nat → StructuredSampleData (PaperHeadSimplex.Tag P) :=
    fun n => (B n).sampleData
  let T : ∀ n, BarycentricTarget (D n) :=
    fun n => (X n).2.2
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar
  let alpha : Nat → Real := fun n =>
    bankPaperCanonicalPostHfitBalancedAlpha
      (B n) c K0 betaProt betaAct
  let fixed : Nat → Finset Nat := fun n =>
    (R n).paperFixedExceptionalFactors deltaStar
  let bankBase : Nat → Finset Nat := fun n =>
    (R n).prechargeBaseState
  let candidates : Nat → Finset Nat := fun n =>
    (R n).roughCanonicalGuardedCandidateSet
      (certificate n) deltaStar (K0 + 1)
  let preSelector : Nat → Nat → Real := fun n =>
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
      (K := K0 + 1) (B n) (R n) (certificate n)
      deltaStar betaProt (alpha n) (betaProt + betaAct)
        (bankPaperCanonicalScaledActiveSeed (T n) (qTilde n))
  let activeSeed : ∀ n, (D n).Sample → Real := fun n =>
    bankPaperCanonicalScaledActiveSeed (T n) (qTilde n)
  let mFrozen : Nat → Real := fun n =>
    bankPaperCanonicalTopFrozenSmoothFrozenMass
      (K := K0 + 1) (B n) (R n) (certificate n)
        deltaStar betaProt (alpha n)
  let Lambda0 : Nat → Real :=
    bankPaperCanonicalActualFrozenLogMassFamily
      D fixed bankBase candidates preSelector activeSeed
  let logY : Nat → Real :=
    F.extendedPrechargedTailLogTarget
  have Hconstructor :
      ∀ᶠ n : Nat in atTop,
        BankPaperCanonicalActualActiveMeasureConstructor
          (D n) (T n) (candidates n) (preSelector n)
            (activeSeed n) := by
    filter_upwards [eventually_ge_atTop N, Hsource] with
        n hn hsourceN
    have hs := hsourceN hn
    dsimp only at hs
    rcases hs with
      ⟨hBn, hBW, hq, hqOne, hsep, hactiveSmooth,
        halpha, hbetaBox, Hresidual, _hprecharged⟩
    have hfinite :=
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_actualActiveMeasureConstructor
        (K := K0 + 1)
        (source n hn).1
        (source n hn).2.1.1
        (source n hn).2.1.2
        (source n hn).2.2
        deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          (source n hn).1 c K0 betaProt betaAct)
        (betaProt + betaAct) (qTilde n)
        hqOne hsep hactiveSmooth halpha hbetaBox
        (fun a ha => (Hresidual.1 a ha).1)
    dsimp only [D, T, B, R, certificate, candidates,
      preSelector, activeSeed, alpha]
    rw [hX n hn]
    exact hfinite
  have Hbalanced :
      ∀ᶠ n : Nat in atTop,
        BankPaperCanonicalTopFrozenBalancedInitialRealization
          depth W K0 n c deltaStar (betaProt + betaAct)
            (fixed n) (bankBase n) (candidates n)
            (preSelector n) := by
    filter_upwards [eventually_ge_atTop N, Hsource] with
        n hn hsourceN
    have hs := hsourceN hn
    dsimp only at hs
    rcases hs with
      ⟨hBn, hBW, hq, _hqOne, _hsep, hactiveSmooth,
        _halpha, _hbetaBox, Hresidual, _hprecharged⟩
    have hvalues :
        ∀ m : (source n hn).1.sampleData.Sample,
          (source n hn).1.sampleData.value m ∈
            (source n hn).2.1.1.roughCanonicalGuardedRow
              (source n hn).2.1.2 deltaStar (K0 + 1) 1 := by
      intro m
      exact hactiveSmooth
        (mem_bankPaperCanonicalStructuredActiveValues.mpr
          ⟨m, rfl⟩)
    have hfinite :=
      bankPaperCanonicalTopFrozenBalancedInitialRealization_of_scaledSeed
        (K0 := K0)
        (source n hn).1
        (source n hn).2.1.1
        (source n hn).2.1.2
        (source n hn).2.2
        deltaStar betaProt betaAct (qTilde n)
        hvalues hq Hresidual.2.1
    dsimp only [fixed, bankBase, candidates, preSelector,
      alpha, B, R, certificate, T]
    rw [hX n hn]
    simpa only [bankPaperCanonicalPostHfitBalancedAlpha,
      hBn, hBW] using hfinite
  have Hgeometry :
      BankPaperCanonicalActualFrozenIntervalGeometry
        (c := c) fixed bankBase candidates := by
    unfold BankPaperCanonicalActualFrozenIntervalGeometry
    filter_upwards [
      eventually_ge_atTop N,
      Hsource,
      eventually_mul_upperTailLength_le_self (K0 + 1) hc]
        with n hn hsourceN hKh
    have hs := hsourceN hn
    dsimp only at hs
    rcases hs with
      ⟨hBn, _hBW, _hq, _hqOne, _hsep, _hactiveSmooth,
        _halpha, _hbetaBox, _Hresidual, _hprecharged⟩
    dsimp only [fixed, bankBase, candidates, R, certificate]
    rw [hX n hn]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have ht :=
        (source n hn).2.1.1.paperFixedExceptionalFactors_subset_tail
          deltaStar ha
      rw [hBn] at ht
      simp only [factorInterval, Finset.mem_Ioc] at ht ⊢
      omega
    · intro a ha
      have hb :=
        (source n hn).2.1.1.prechargeBaseState_subset_factorInterval ha
      simpa only [hBn] using hb
    · intro a ha
      have hKhB :
          (K0 + 1) *
                upperTailLength c (source n hn).1.sampleData.n ≤
              (source n hn).1.sampleData.n := by
        simpa only [hBn] using hKh
      have hraw :=
        (source n hn).2.1.1
          |>.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
            (source n hn).2.1.2 deltaStar (K0 + 1) ha
      rw [roughRawCandidateSet_eq_Ioc hKhB] at hraw
      simp only [factorInterval, Finset.mem_Ioc] at hraw ⊢
      unfold upperEndpoint
      omega
  have Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
            (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde) := by
    simpa only [qTilde, logY, Lambda0, activeSeed] using
      (bankPaperCanonicalSectionNinePostHeight_sourceFirstAnalyticLedger_of_actualData
        (betaAct := betaAct)
        (betaTotal := betaProt + betaAct)
        hc hdeltaStar hdeltaStarUpper
        depth W K0 1
        F D T fixed bankBase candidates preSelector mFrozen
        Hconstructor Hgeometry Hbalanced)
  refine ⟨logY, Lambda0, mFrozen, rfl, Hledger, ?_⟩
  filter_upwards [Hsource] with n hsourceN
  intro hn
  have hs := hsourceN hn
  dsimp only at hs
  rcases hs with
    ⟨_hBn, _hBW, _hq, _hqOne, _hsep, hactiveSmooth,
      _halpha, _hbetaBox, _Hresidual, hprecharged⟩
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [mFrozen, alpha, B, R, certificate]
    rw [hX n hn]
  · rw [show logY n = F.extendedPrechargedTailLogTarget n by rfl,
      F.extendedPrechargedTailLogTarget_eq hn,
      ← hprecharged]
    rfl
  · have hround :=
      bankPaperCanonicalTopFrozenRounded_actualFrozenLogMass_eq_qTildeSource
        (K := K0 + 1)
        (source n hn).1
        (source n hn).2.1.1
        (source n hn).2.1.2
        ((source n hn).2.1.1.paperFixedExceptionalFactors deltaStar)
        (source n hn).2.1.1.prechargeBaseState
        (source n hn).2.2
        deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          (source n hn).1 c K0 betaProt betaAct)
        (betaProt + betaAct) (qTilde n) hactiveSmooth
    calc
      Lambda0 n =
          bankPaperCanonicalActualFrozenLogMass
            (source n hn).1.sampleData
            ((source n hn).2.1.1.paperFixedExceptionalFactors deltaStar)
            (source n hn).2.1.1.prechargeBaseState
            ((source n hn).2.1.1.roughCanonicalGuardedCandidateSet
              (source n hn).2.1.2 deltaStar (K0 + 1))
            (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
              (K := K0 + 1)
              (source n hn).1
              (source n hn).2.1.1
              (source n hn).2.1.2
              deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                (source n hn).1 c K0 betaProt betaAct)
              (betaProt + betaAct)
              (bankPaperCanonicalScaledActiveSeed
                (source n hn).2.2 (qTilde n)))
            (bankPaperCanonicalScaledActiveSeed
              (source n hn).2.2 (qTilde n)) := by
        dsimp only [Lambda0,
          bankPaperCanonicalActualFrozenLogMassFamily,
          D, fixed, bankBase, candidates, preSelector, activeSeed,
          T, alpha, B, R, certificate]
        rw [hX n hn]
      _ =
          bankPaperCanonicalActualFrozenLogMass
            (source n hn).1.sampleData
            ((source n hn).2.1.1.paperFixedExceptionalFactors deltaStar)
            (source n hn).2.1.1.prechargeBaseState
            ((source n hn).2.1.1.roughCanonicalGuardedCandidateSet
              (source n hn).2.1.2 deltaStar (K0 + 1))
            (bankPaperCanonicalTopFrozenRoundedSourceSelector
              (K := K0 + 1)
              (source n hn).1
              (source n hn).2.1.1
              (source n hn).2.1.2
              (source n hn).2.2
              deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                (source n hn).1 c K0 betaProt betaAct)
              (betaProt + betaAct) (qTilde n))
            (bankPaperCanonicalTopFrozenRoundedActiveSeed
              (K := K0 + 1)
              (source n hn).1
              (source n hn).2.1.1
              (source n hn).2.1.2
              (source n hn).2.2
              deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                (source n hn).1 c K0 betaProt betaAct)
              (qTilde n)) :=
        hround.symm
      _ =
          bankPaperCanonicalSectionNinePostHeightRoundedLambda0
            (K0 + 1)
            (source n hn).1
            (source n hn).2.1.1
            (source n hn).2.1.2
            (source n hn).2.2
            deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              (source n hn).1 c K0 betaProt betaAct)
            (betaProt + betaAct) (qTilde n) := by
        unfold bankPaperCanonicalSectionNinePostHeightRoundedLambda0
        rw [(source n hn).2.1.1.baseExactificationBank_eq_prechargeBaseState]

end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal005_001.{u_1} := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstLedgerFamilies
