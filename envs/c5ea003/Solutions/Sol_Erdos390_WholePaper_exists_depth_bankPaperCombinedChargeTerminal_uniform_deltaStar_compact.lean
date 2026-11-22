-- Prove2me | solution 1 for Erdos390.WholePaper.exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:43:51.730688+00:00
-- url     : https://prove2.me/submissions/13bb8479-b88f-4acf-beba-c2c33ddb650c

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
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_eventually_paperExceptionalChargeEpsilon_le_power
import Theorems.Thm_Erdos390_WholePaper_eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant
import Theorems.Thm_Erdos390_WholePaper_exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve_compact


section
theorem Erdos390.WholePaper.exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve : Erdos390.RemainingAnalyticGoal008_011 := @Erdos390.WholePaper.exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve_compact
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



namespace GuardedCentralAnchorCertificate



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

/- Source module: Erdos390.WholePaper.BankPaperSelectorTailTarget -/
section


/-!
# The residual selector target after all base charges

The guarded central anchors are charged before `prechargedTailTarget` is
formed.  Fractional selection starts only after an independently fixed
factor set and the literal state-zero exactification bank have also been
charged.  This file names that second quotient and records the exact
division-free and valuation interfaces used by the post-tangent
certificate.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization



/-- The generic exactification notation for the selector charge is exactly
the concrete precharged bank product. -/
theorem selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct
    {n M : ℕ} (R : BankPaperRealization n M)
    (fixed : Finset ℕ) :
    R.selectorTailCharge fixed =
      fixed.prod id * R.prechargeBaseStateProduct := by
  rw [selectorTailCharge,
    R.baseExactificationBank_prod_eq_prechargeBaseStateProduct]

/-- Positivity of the selector charge follows from positivity of the
caller's fixed factors and interval positivity of every actual precharged
bank factor. -/
theorem selectorTailCharge_pos
    {n M : ℕ} (R : BankPaperRealization n M)
    (fixed : Finset ℕ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a) :
    0 < R.selectorTailCharge fixed := by
  rw [R.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct]
  apply Nat.mul_pos
  · exact Finset.prod_pos fun a ha ↦ by
      simpa only [id_eq] using hfixedPositive a ha
  · rw [prechargeBaseStateProduct]
    apply Finset.prod_pos
    intro factor hfactor
    have hinterval := R.prechargeBaseState_subset_factorInterval hfactor
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1

end BankPaperRealization

namespace GuardedCentralAnchorCertificate





/-- Division-free recovery of the precharged tail from the residual
selector target and its complete base charge. -/
theorem selectorTailTarget_mul_selectorTailCharge
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget) :
    certificate.selectorTailTarget R fixed *
        R.selectorTailCharge fixed =
      certificate.prechargedTailTarget := by
  rw [selectorTailTarget]
  exact Nat.div_mul_cancel hchargeDvd





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

/-- The set difference in the definition makes the fixed factors and all
designated donors literally disjoint. -/
theorem paperFixedExceptionalFactors_disjoint_prechargeDonorSet
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (R.paperFixedExceptionalFactors deltaStar)
      R.prechargeDonorSet := by
  rw [Finset.disjoint_left]
  intro a haFixed haDonor
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at haFixed
  exact haFixed.2 haDonor

/-- Fixed exceptional factors together with their complementary donor
occurrences remain a subset of the literal upper tail. -/
theorem paperFixedExceptionalBacking_subset_tail
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ∪ R.prechargeDonorSet ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) := by
  intro a ha
  rcases Finset.mem_union.mp ha with haFixed | haDonor
  · exact R.paperFixedExceptionalFactors_subset_tail deltaStar haFixed
  · exact R.prechargeDonorSet_subset_tail haDonor

/-- The backing union is an actual subset-product of the factorial tail. -/
theorem paperFixedExceptionalBacking_prod_dvd_centralTailProduct
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    (R.paperFixedExceptionalFactors deltaStar ∪
        R.prechargeDonorSet).prod id ∣
      centralTailProduct n h := by
  change (R.paperFixedExceptionalFactors deltaStar ∪
      R.prechargeDonorSet).prod id ∣
    (Finset.Ioc (2 * n) (2 * n + h)).prod id
  exact Finset.prod_dvd_prod_of_subset
    (R.paperFixedExceptionalFactors deltaStar ∪ R.prechargeDonorSet)
    (Finset.Ioc (2 * n) (2 * n + h)) id
    (by
      simpa only [upperEndpoint] using
        R.paperFixedExceptionalBacking_subset_tail deltaStar)

/-- Product form of the disjoint fixed-factor/donor ownership ledger. -/
theorem paperFixedExceptionalFactors_prod_mul_prechargeDonorSet_prod
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    (R.paperFixedExceptionalFactors deltaStar).prod id *
        R.prechargeDonorSet.prod id =
      (R.paperFixedExceptionalFactors deltaStar ∪
        R.prechargeDonorSet).prod id := by
  rw [Finset.prod_union
    (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet deltaStar)]

private theorem paperFixedExceptionalFactors_prod_pos
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    0 < (R.paperFixedExceptionalFactors deltaStar).prod id := by
  apply Finset.prod_pos
  intro factor hfactor
  have htail := R.paperFixedExceptionalFactors_subset_tail deltaStar hfactor
  exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1

private theorem prechargeBaseStateProduct_pos
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    0 < R.prechargeBaseStateProduct := by
  rw [prechargeBaseStateProduct]
  apply Finset.prod_pos
  intro factor hfactor
  have hinterval := R.prechargeBaseState_subset_factorInterval hfactor
  exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1

private theorem prechargeDonorSet_prod_pos
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    0 < R.prechargeDonorSet.prod id := by
  apply Finset.prod_pos
  intro factor hfactor
  have htail := R.prechargeDonorSet_subset_tail hfactor
  exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1

/-- Strong high-prime backing identity.  In every coordinate above `y`, the
complete selector charge has exactly the valuation of the disjoint union of
the retained exceptional tail factors and the actual donors they complement.
-/
theorem paperFixedExceptional_selectorTailCharge_factorization_eq_backing
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (hp : yNat n < p) :
    (R.selectorTailCharge
        (R.paperFixedExceptionalFactors deltaStar)).factorization p =
      ((R.paperFixedExceptionalFactors deltaStar ∪
        R.prechargeDonorSet).prod id).factorization p := by
  have hfixedNe :
      (R.paperFixedExceptionalFactors deltaStar).prod id ≠ 0 :=
    (paperFixedExceptionalFactors_prod_pos R deltaStar).ne'
  have hbaseNe : R.prechargeBaseStateProduct ≠ 0 :=
    (prechargeBaseStateProduct_pos R).ne'
  have hdonorNe : R.prechargeDonorSet.prod id ≠ 0 :=
    (prechargeDonorSet_prod_pos R).ne'
  rw [R.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct,
    ← R.paperFixedExceptionalFactors_prod_mul_prechargeDonorSet_prod
      deltaStar,
    Nat.factorization_mul hfixedNe hbaseNe,
    Nat.factorization_mul hfixedNe hdonorNe,
    Finsupp.add_apply, Finsupp.add_apply,
    R.prechargeBaseStateProduct_factorization_eq_donorSet_prod hp]

/-- Unconditional high-prime half of the paper's combined-charge argument.
The missing low-prime exceptional-charge estimate is neither assumed nor
hidden in this statement. -/
theorem paperFixedExceptional_selectorTailCharge_factorization_le
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (hp : yNat n < p) :
    (R.selectorTailCharge
        (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
      (centralTailProduct n h).factorization p := by
  rw [R.paperFixedExceptional_selectorTailCharge_factorization_eq_backing
    deltaStar hp]
  have hbackingPos :
      0 < (R.paperFixedExceptionalFactors deltaStar ∪
        R.prechargeDonorSet).prod id := by
    apply Finset.prod_pos
    intro factor hfactor
    have htail := R.paperFixedExceptionalBacking_subset_tail deltaStar hfactor
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1
  exact (Nat.factorization_le_iff_dvd hbackingPos.ne'
    (centralTailProduct_pos n h).ne').mpr
      (R.paperFixedExceptionalBacking_prod_dvd_centralTailProduct
        deltaStar) p

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

















/-! ## The exact endpoint remainder, with constant one -/













/-! ## Exact factorization of exceptional common multipliers -/























/-! ## Substitution of the verified abstract sieve bound -/

















/-! ## The `delta_* < 1/18`, `y^4=n^(8/9)` remainder arithmetic -/





/-- The numerical threshold in Section 9 leaves the explicit power saving
`delta_* + 8/9 - 1 < -1/18`. -/
theorem tangentExceptional_deltaStar_remainder_exponent
    {deltaStar : ℝ} (hdeltaStar : deltaStar < 1 / 18) :
    deltaStar + 8 / 9 - 1 < -(1 / 18 : ℝ) := by
  linarith

/-- In particular the power occurring before the harmless logarithmic
denominator tends to zero. -/
theorem tangentExceptional_remainderPower_tendsto_zero
    {deltaStar : ℝ} (hdeltaStar : deltaStar < 1 / 18) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (deltaStar + 8 / 9 - 1))
      atTop (nhds 0) := by
  have hexponent : deltaStar + 8 / 9 - 1 < 0 :=
    (tangentExceptional_deltaStar_remainder_exponent hdeltaStar).trans
      (by norm_num)
  have h :=
    (tendsto_rpow_neg_atTop (neg_pos.mpr hexponent)).comp
      tendsto_natCast_atTop_atTop
  simpa only [neg_neg] using h

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





theorem paperExceptionalChargeEpsilon_nonneg
    (deltaStar : ℝ) (n : ℕ) :
    0 ≤ paperExceptionalChargeEpsilon deltaStar n := by
  unfold paperExceptionalChargeEpsilon
  have hC : 0 ≤ paperExceptionalSelbergRemainderConstant :=
    paperExceptionalSelbergRemainderConstant_pos.le
  positivity



/-- The literal remainder term is exactly `epsilon(n) N/(pL)`. -/
theorem paperExceptionalFiniteRemainder_eq_epsilon_mul_scale
    {deltaStar : ℝ} {n p : ℕ}
    (hn : 1 < n) (hp : 0 < p)
    (hlogY : 0 < Real.log (yNat n : ℝ)) :
    4 * paperExceptionalSelbergRemainderConstant *
          (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 /
        ((p : ℝ) * Real.log (yNat n : ℝ) ^ 2) =
      paperExceptionalChargeEpsilon deltaStar n *
        secondOrderScale n / ((p : ℝ) * L n) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hL : 0 < L n := L_pos hn
  unfold paperExceptionalChargeEpsilon secondOrderScale
  rw [show Real.log (n : ℝ) = L n by rfl]
  field_simp [hnR.ne', hpR.ne', hL.ne', hlogY.ne']

/-! ## The endpoint remainder tends to zero -/



/-- The endpoint/remainder coefficient is genuinely `o(1)` when
`0 ≤ deltaStar < 1/18`. -/
theorem paperExceptionalChargeEpsilon_tendsto_zero
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    Tendsto (paperExceptionalChargeEpsilon deltaStar)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall
      (paperExceptionalChargeEpsilon_nonneg deltaStar)
  · exact eventually_paperExceptionalChargeEpsilon_le_power
      hdeltaNonneg
  · simpa only [mul_zero] using
      (tangentExceptional_remainderPower_tendsto_zero
        hdeltaUpper).const_mul
          (200 * paperExceptionalSelbergRemainderConstant)

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



/-- The finite Selberg main term fits inside the paper's displayed
`A_exc*(deltaStar/theta)*N/p` reserve.  The constants deliberately retain
the paper's slack: the finite calculation gives `40*c*C_S`, whereas
`A_exc/theta=72*c*C_S`. -/
theorem paperExceptionalFiniteChargeMain_le_paperReserve
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar)
    {n p : ℕ} (hn : 1 < n) (hp : 0 < p)
    (hlogY : (1 / 5 : ℝ) * L n ≤
      Real.log (yNat n : ℝ))
    (htail : (upperTailLength c n : ℝ) ≤
      2 * c * secondOrderScale n) :
    4 * paperExceptionalSelbergMainConstant * deltaStar * L n *
          (upperTailLength c n : ℝ) /
        ((p : ℝ) * Real.log (yNat n : ℝ)) ≤
      paperExceptionalChargeConstant c *
        (deltaStar / paperExceptionalTheta) *
        secondOrderScale n / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hL : 0 < L n := L_pos hn
  have hscale : 0 < secondOrderScale n :=
    secondOrderScale_pos (by omega)
  have hlogYPos : 0 < Real.log (yNat n : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL).trans_le hlogY
  have htailDiv :
      (upperTailLength c n : ℝ) / (p : ℝ) ≤
        (2 * c * secondOrderScale n) / (p : ℝ) :=
    div_le_div_of_nonneg_right htail hpR.le
  have hLlog :
      L n / Real.log (yNat n : ℝ) ≤ 5 := by
    apply (div_le_iff₀ hlogYPos).2
    nlinarith [hlogY]
  have hcoefficient :
      0 ≤ 4 * paperExceptionalSelbergMainConstant * deltaStar := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) paperExceptionalSelbergMainConstant_pos.le)
      hdelta.le
  have hLlogNonneg :
      0 ≤ L n / Real.log (yNat n : ℝ) := by positivity
  have hbase : 0 ≤
      c * paperExceptionalSelbergMainConstant * deltaStar *
        secondOrderScale n / (p : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hc.le paperExceptionalSelbergMainConstant_pos.le)
          hdelta.le)
        hscale.le)
      hpR.le
  calc
    4 * paperExceptionalSelbergMainConstant * deltaStar * L n *
          (upperTailLength c n : ℝ) /
        ((p : ℝ) * Real.log (yNat n : ℝ)) =
      (4 * paperExceptionalSelbergMainConstant * deltaStar) *
        ((upperTailLength c n : ℝ) / (p : ℝ)) *
        (L n / Real.log (yNat n : ℝ)) := by
      field_simp [hpR.ne', hlogYPos.ne']
    _ ≤ (4 * paperExceptionalSelbergMainConstant * deltaStar) *
        ((2 * c * secondOrderScale n) / (p : ℝ)) *
        (L n / Real.log (yNat n : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htailDiv hcoefficient)
        hLlogNonneg
    _ ≤ (4 * paperExceptionalSelbergMainConstant * deltaStar) *
        ((2 * c * secondOrderScale n) / (p : ℝ)) * 5 :=
      mul_le_mul_of_nonneg_left hLlog
        (mul_nonneg hcoefficient
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc.le)
            hscale.le) hpR.le))
    _ = 40 *
        (c * paperExceptionalSelbergMainConstant * deltaStar *
          secondOrderScale n / (p : ℝ)) := by ring
    _ ≤ 72 *
        (c * paperExceptionalSelbergMainConstant * deltaStar *
          secondOrderScale n / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right (by norm_num) hbase
    _ = paperExceptionalChargeConstant c *
        (deltaStar / paperExceptionalTheta) *
        secondOrderScale n / (p : ℝ) := by
      norm_num [paperExceptionalChargeConstant, paperExceptionalTheta]
      ring

/-- Uniform asymptotic packaging of the canonical finite majorant.  This is
the theorem to compose with the finite weighted-fibre estimate; it does not
postulate that estimate. -/
theorem eventually_paperExceptionalFiniteChargeMajorant_le
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0 < p →
      paperExceptionalFiniteChargeMajorant c deltaStar n p ≤
        paperExceptionalChargeConstant c *
            (deltaStar / paperExceptionalTheta) *
            secondOrderScale n / (p : ℝ) +
          paperExceptionalChargeEpsilon deltaStar n *
            secondOrderScale n / ((p : ℝ) * L n) := by
  filter_upwards
    [eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc]
      with n hn hlogY htail
  intro p hp
  have hlogYPos : 0 < Real.log (yNat n : ℝ) := by
    have hL : 0 < L n := L_pos (by omega)
    exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL).trans_le hlogY
  have hmain := paperExceptionalFiniteChargeMain_le_paperReserve
    hc hdelta (n := n) (p := p) (by omega) hp hlogY htail
  have hremainder := paperExceptionalFiniteRemainder_eq_epsilon_mul_scale
    (deltaStar := deltaStar) (n := n) (p := p) (by omega) hp hlogYPos
  unfold paperExceptionalFiniteChargeMajorant
  calc
    4 * paperExceptionalSelbergMainConstant * deltaStar * L n *
          (upperTailLength c n : ℝ) /
        ((p : ℝ) * Real.log (yNat n : ℝ)) +
        4 * paperExceptionalSelbergRemainderConstant *
          (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 /
        ((p : ℝ) * Real.log (yNat n : ℝ) ^ 2) ≤
      paperExceptionalChargeConstant c *
          (deltaStar / paperExceptionalTheta) *
          secondOrderScale n / (p : ℝ) +
        4 * paperExceptionalSelbergRemainderConstant *
          (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 /
        ((p : ℝ) * Real.log (yNat n : ℝ) ^ 2) :=
      add_le_add_left hmain _
    _ = paperExceptionalChargeConstant c *
          (deltaStar / paperExceptionalTheta) *
          secondOrderScale n / (p : ℝ) +
        paperExceptionalChargeEpsilon deltaStar n *
          secondOrderScale n / ((p : ℝ) * L n) := by
      rw [hremainder]

/-! ## Exact support cutoff for the actual fixed charge -/







/-! ## Closing the finite weighted Selberg estimate -/



/-- Canonical paper-facing low-prime charge package.  The error coefficient
tends to zero under `deltaStar<1/18`, and the displayed valuation inequality
is simultaneous for every realized bank and every prime `p≤yNat n`. -/
theorem paperFixedExceptionalCharge_asymptoticPackage
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    Tendsto (paperExceptionalChargeEpsilon deltaStar) atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n))) (p : ℕ),
          p.Prime → p ≤ yNat n →
          (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
              ℝ) ≤
            paperExceptionalChargeConstant c *
                (deltaStar / paperExceptionalTheta) *
                secondOrderScale n / (p : ℝ) +
              paperExceptionalChargeEpsilon deltaStar n *
                secondOrderScale n / ((p : ℝ) * L n) := by
  refine ⟨paperExceptionalChargeEpsilon_tendsto_zero
    hdelta.le hdeltaUpper, ?_⟩
  filter_upwards
    [eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant
      hc hdelta,
      eventually_paperExceptionalFiniteChargeMajorant_le hc hdelta]
      with n hfinite hmajorant
  intro R p hpPrime hpLow
  exact (hfinite R p hpPrime hpLow).trans (hmajorant p hpPrime.pos)









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCombinedChargeTerminal -/
section


/-!
# The honest combined fixed-factor and precharge terminal

The precharge terminal leaves one twelfth of the `c-C0` valuation reserve
after the base bank has been charged on the fixed anchor support.  The
literal fixed exceptional factors use at most one twenty-fourth of that
reserve for a sufficiently small positive `deltaStar`; hence another
twenty-fourth remains after the complete selector charge.

Away from the fixed anchor support there is no anchor valuation.  For primes
up to `yNat`, the fixed exceptional estimate is combined with the already
proved moving-prime `o(secondOrderScale)` bank/Legendre cost.  Above `yNat`,
the exact donor-backing identity pays the complete selector charge directly
from the literal upper tail.  Thus the conclusion below is actual natural
divisibility, with no divisibility or charge-bound premise.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## An explicit admissible exceptional exponent -/











/-! ## Uniform low-prime fixed charge -/

/-- Under the explicit numerical range, the complete fixed exceptional
product eventually costs at most one twenty-fourth of `c-C0`, uniformly at
every prime up to `yNat`.  This is the finite Selberg/valuation theorem plus
its proved vanishing endpoint remainder, not an assumed charge bound. -/
theorem eventually_paperFixedExceptionalFactors_charge_le_combinedReserve
    {c deltaStar : ℝ} (hc : C0 < c)
    (hdelta : IsPaperCombinedChargeDeltaStar c deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) (p : ℕ),
        p.Prime → p ≤ yNat n →
        (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
            ℝ) ≤
          (c - C0) / 24 * secondOrderScale n / (p : ℝ) := by
  have hC0Pos : (0 : ℝ) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hgap : 0 < c - C0 := sub_pos.mpr hc
  obtain ⟨hepsilonZero, hcharge⟩ :=
    paperFixedExceptionalCharge_asymptoticPackage
      hcPos hdelta.1 hdelta.2.1
  have hepsilonSmall : ∀ᶠ n : ℕ in atTop,
      paperExceptionalChargeEpsilon deltaStar n < (c - C0) / 48 :=
    hepsilonZero.eventually (eventually_lt_nhds (by positivity))
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLOne : ∀ᶠ n : ℕ in atTop, 1 ≤ L n :=
    hLTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hcharge, hepsilonSmall, hLOne,
      eventually_secondOrderScale_pos]
      with n hchargeN hepsilonN hLOneN hscale
  intro R p hpPrime hpLow
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hLPos : 0 < L n := zero_lt_one.trans_le hLOneN
  have hepsilonNonneg :
      0 ≤ paperExceptionalChargeEpsilon deltaStar n :=
    paperExceptionalChargeEpsilon_nonneg deltaStar n
  have hepsilonDiv :
      paperExceptionalChargeEpsilon deltaStar n / L n ≤
        (c - C0) / 48 := by
    calc
      paperExceptionalChargeEpsilon deltaStar n / L n ≤
          paperExceptionalChargeEpsilon deltaStar n :=
        div_le_self hepsilonNonneg hLOneN
      _ ≤ (c - C0) / 48 := hepsilonN.le
  have hmain :
      paperExceptionalChargeConstant c *
            (deltaStar / paperExceptionalTheta) *
            secondOrderScale n / (p : ℝ) ≤
        (c - C0) / 48 * secondOrderScale n / (p : ℝ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hdelta.2.2 hscale.le) hpR.le
  have herror :
      paperExceptionalChargeEpsilon deltaStar n *
            secondOrderScale n / ((p : ℝ) * L n) ≤
        (c - C0) / 48 * secondOrderScale n / (p : ℝ) := by
    calc
      paperExceptionalChargeEpsilon deltaStar n *
            secondOrderScale n / ((p : ℝ) * L n) =
          (paperExceptionalChargeEpsilon deltaStar n / L n) *
            secondOrderScale n / (p : ℝ) := by
        field_simp [hpR.ne', hLPos.ne']
      _ ≤ (c - C0) / 48 * secondOrderScale n / (p : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hepsilonDiv hscale.le) hpR.le
  calc
    (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
        ℝ) ≤
      paperExceptionalChargeConstant c *
            (deltaStar / paperExceptionalTheta) *
            secondOrderScale n / (p : ℝ) +
        paperExceptionalChargeEpsilon deltaStar n *
            secondOrderScale n / ((p : ℝ) * L n) :=
      hchargeN R p hpPrime hpLow
    _ ≤ (c - C0) / 48 * secondOrderScale n / (p : ℝ) +
        (c - C0) / 48 * secondOrderScale n / (p : ℝ) :=
      add_le_add hmain herror
    _ = (c - C0) / 24 * secondOrderScale n / (p : ℝ) := by
      ring

/-! ## Combined terminal -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCombinedChargeDepthFirstTerminal -/
section


/-!
# Depth-first combined charge terminal

The original combined-charge terminal specializes `deltaStar` before it
exposes the capacity depth.  For the Section 9 clean-list application this
creates an artificial cycle: the clean-list width `W` must dominate the
chosen depth, while the tangent-compatible `deltaStar` is defined using
`W`.

The strengthened precharge-capacity theorem actually chooses its depth
using only `c`.  This file preserves that proof order.  It first fixes one
capacity depth and then proves the complete combined-charge conclusion
uniformly for every admissible `deltaStar`.  The tangent-choice corollary
therefore allows `W` and `r0` to be chosen after the depth is known.

The payload also retains the base exactification-bank divisibility fact
needed by `BankPaperCanonicalPostTangentContinuationAtDepth`; the older
combined-charge terminal discarded this already-proved capacity fact.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Fixed-depth payload -/



/-! ## Uniform admissible exponent after capacity -/

set_option maxHeartbeats 800000 in
/-- One capacity depth works for every combined-charge-admissible
`deltaStar`.  In particular, the exponent may be chosen after the depth. -/
theorem exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar
    {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ deltaStar : ℝ, IsPaperCombinedChargeDeltaStar c deltaStar →
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth := by
  have hC0Pos : (0 : ℝ) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hgap : 0 < c - C0 := sub_pos.mpr hc
  obtain ⟨depth, hdepth, hprecharge⟩ :=
    exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve hc
  have hsupportCutoff :=
    eventually_bankAnchor_fixed_le_yNat (2 * depth + 1)
  have hcapacitySmall :=
    (bankPaperPrechargeUniformCapacityCost_normalized_tendsto_zero hcPos).eventually
      (eventually_lt_nhds (by positivity : (0 : ℝ) < c / 4))
  have htailLarge :=
    (upperTailLength_normalized_tendsto hcPos).eventually
      (eventually_gt_nhds (by linarith : c / 2 < c))
  have hendpoint := eventually_upperScaledEndpoint_bounds hcPos
  refine ⟨depth, hdepth, ?_⟩
  intro deltaStar hdelta
  have hfixedCharge :=
    eventually_paperFixedExceptionalFactors_charge_le_combinedReserve
      hc hdelta
  simp only [BankPaperCombinedChargeTerminalAtDepth]
  filter_upwards [hprecharge, hfixedCharge, hsupportCutoff,
      hcapacitySmall, htailLarge, hendpoint,
      eventually_secondOrderScale_pos]
      with n hprechargeN hfixedChargeN hsupportN hcapacityN htailN
        hendpointN hscale
  obtain ⟨bank, certificate, hanchorBank, hretainedBefore,
      hretainedTarget, hbaseDvd, htargetIdentity⟩ := hprechargeN
  let fixed : Finset ℕ := bank.paperFixedExceptionalFactors deltaStar
  let charge : ℕ := bank.selectorTailCharge fixed
  let divisor : ℕ :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  let tail : ℕ := centralTailProduct n (upperTailLength c n)
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    have htail := bank.paperFixedExceptionalFactors_subset_tail
      deltaStar (by simpa only [fixed] using ha)
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1
  have hfixedProdPos : 0 < fixed.prod id := by
    apply Finset.prod_pos
    intro a ha
    simpa only [id_eq] using hfixedPositive a ha
  have hbasePos : 0 < bank.prechargeBaseStateProduct := by
    rw [BankPaperRealization.prechargeBaseStateProduct]
    apply Finset.prod_pos
    intro factor hfactor
    have hinterval := bank.prechargeBaseState_subset_factorInterval hfactor
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1
  have hchargePos : 0 < charge := by
    exact bank.selectorTailCharge_pos fixed hfixedPositive
  have hdivisorPos : 0 < divisor := by
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  have htailPos : 0 < tail := by
    exact centralTailProduct_pos n (upperTailLength c n)
  have hchargeFactorization : ∀ p : ℕ,
      charge.factorization p =
        (fixed.prod id).factorization p +
          bank.prechargeBaseStateProduct.factorization p := by
    intro p
    dsimp only [charge]
    rw [bank.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct,
      Nat.factorization_mul hfixedProdPos.ne' hbasePos.ne',
      Finsupp.add_apply]
  have hdivisorHigh : ∀ p, p.Prime → yNat n < p →
      divisor.factorization p = 0 := by
    intro p hpPrime hpHigh
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpDvd
    have hpSupport := certificate.divisor_prime_support p hpPrime
      (by simpa only [divisor] using hpDvd)
    have hpLe := (mem_primesUpTo.mp hpSupport).2
    omega
  have hlow : ∀ p, p.Prime → p ≤ yNat n →
      divisor.factorization p + charge.factorization p ≤
        tail.factorization p := by
    intro p hpPrime hpLow
    have hpPos : 0 < p := hpPrime.pos
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPos
    have hpredPosNat : 0 < p - 1 := Nat.sub_pos_of_lt hpPrime.one_lt
    have hpredPos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpredPosNat
    have hpredLe : (((p - 1 : ℕ) : ℝ)) ≤ (p : ℝ) := by
      exact_mod_cast Nat.sub_le p 1
    have hfixedP := hfixedChargeN bank p hpPrime hpLow
    have hfixedPred :
        ((fixed.prod id).factorization p : ℝ) ≤
          (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n := by
      have hinv : 1 / (p : ℝ) ≤
          1 / (((p - 1 : ℕ) : ℝ)) :=
        one_div_le_one_div_of_le hpredPos hpredLe
      calc
        ((fixed.prod id).factorization p : ℝ) ≤
            (c - C0) / 24 * secondOrderScale n / (p : ℝ) := by
          simpa only [fixed] using hfixedP
        _ = ((c - C0) / 24 * secondOrderScale n) *
              (1 / (p : ℝ)) := by ring
        _ ≤ ((c - C0) / 24 * secondOrderScale n) *
              (1 / (((p - 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hinv
            (mul_nonneg (by positivity) hscale.le)
        _ = (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
              secondOrderScale n := by
          field_simp [hpredPos.ne']
    by_cases hpSupport : p ∈ primesUpTo (2 * depth + 1)
    · have hretained := hretainedBefore p hpSupport
      have hcombinedReal :
          ((divisor.factorization p + charge.factorization p : ℕ) : ℝ) ≤
            (upperTailValuation c n p : ℝ) := by
        have hchargeCast : (charge.factorization p : ℝ) =
            ((fixed.prod id).factorization p : ℝ) +
              (bank.prechargeBaseStateProduct.factorization p : ℝ) := by
          exact_mod_cast hchargeFactorization p
        have hreserveNonneg : 0 ≤
            (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
              secondOrderScale n := by positivity
        rw [Nat.cast_add, hchargeCast]
        calc
          (divisor.factorization p : ℝ) +
                (((fixed.prod id).factorization p : ℝ) +
                  (bank.prechargeBaseStateProduct.factorization p : ℝ)) ≤
              (divisor.factorization p : ℝ) +
                ((c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
                  secondOrderScale n) +
                (bank.prechargeBaseStateProduct.factorization p : ℝ) := by
            linarith
          _ ≤ (divisor.factorization p : ℝ) +
                ((c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
                  secondOrderScale n) +
                (bank.prechargeBaseStateProduct.factorization p : ℝ) := by
            have htwice :
                (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
                    secondOrderScale n =
                  2 * ((c - C0) /
                    (24 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n) := by
              field_simp [hpredPos.ne']
              ; ring
            rw [htwice]
            linarith
          _ ≤ (upperTailValuation c n p : ℝ) := by
            have hretained' := hretained
            simp only [Nat.cast_add] at hretained'
            linarith
      dsimp only [tail]
      rw [← upperTailValuation_eq_centralTailProduct_factorization]
      exact_mod_cast hcombinedReal
    · have hdivisorZero : divisor.factorization p = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hpDvd
        exact hpSupport
          (certificate.divisor_prime_support p hpPrime
            (by simpa only [divisor] using hpDvd))
      rw [hdivisorZero, zero_add]
      have hbaseBound :=
        bank.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
          hpPrime hendpointN.2
      have hchargeCost :
          (p - 1) *
              (charge.factorization p + Nat.log2 (upperTailLength c n) + 1) ≤
            upperTailLength c n := by
        have hchargeBoundNat :
            charge.factorization p ≤
              (fixed.prod id).factorization p +
                bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) := by
          rw [hchargeFactorization p]
          exact Nat.add_le_add_left hbaseBound _
        have hpredFixed :
            (((p - 1) * (fixed.prod id).factorization p : ℕ) : ℝ) ≤
              (c - C0) / 24 * secondOrderScale n := by
          rw [Nat.cast_mul]
          calc
            (((p - 1 : ℕ) : ℝ)) *
                  ((fixed.prod id).factorization p : ℝ) ≤
                (((p - 1 : ℕ) : ℝ)) *
                  ((c - C0) / 24 * secondOrderScale n / (p : ℝ)) :=
              mul_le_mul_of_nonneg_left
                (by simpa only [fixed] using hfixedP)
                (Nat.cast_nonneg _)
            _ = ((c - C0) / 24 * secondOrderScale n) *
                ((((p - 1 : ℕ) : ℝ)) / (p : ℝ)) := by ring
            _ ≤ ((c - C0) / 24 * secondOrderScale n) * 1 := by
              apply mul_le_mul_of_nonneg_left
              · exact (div_le_one hpR).2 hpredLe
              · positivity
            _ = (c - C0) / 24 * secondOrderScale n := by ring
        have hpredOverheadNat :
            (p - 1) *
                (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                  Nat.log2 (upperTailLength c n) + 1) ≤
              bankPaperPrechargeUniformCapacityCost c n := by
          rw [bankPaperPrechargeUniformCapacityCost,
            Nat.log2_eq_log_two]
          exact Nat.mul_le_mul_right _
            ((Nat.sub_le p 1).trans hpLow)
        have hcapacityCast :
            (bankPaperPrechargeUniformCapacityCost c n : ℝ) <
              c / 4 * secondOrderScale n := by
          exact (div_lt_iff₀ hscale).mp hcapacityN
        have htailCast :
            c / 2 * secondOrderScale n <
              (upperTailLength c n : ℝ) := by
          exact (lt_div_iff₀ hscale).mp htailN
        have hoverheadCast :
            (((p - 1) *
                (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                  Nat.log2 (upperTailLength c n) + 1) : ℕ) : ℝ) ≤
              (bankPaperPrechargeUniformCapacityCost c n : ℝ) := by
          exact_mod_cast hpredOverheadNat
        have hcoeff :
            (c - C0) / 24 + c / 4 < c / 2 := by
          nlinarith
        have hsum :
            (((p - 1) * (fixed.prod id).factorization p : ℕ) : ℝ) +
                (((p - 1) *
                  (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                    Nat.log2 (upperTailLength c n) + 1) : ℕ) : ℝ) <
              c / 2 * secondOrderScale n := by
          calc
            _ ≤ (c - C0) / 24 * secondOrderScale n +
                  (bankPaperPrechargeUniformCapacityCost c n : ℝ) :=
              add_le_add hpredFixed hoverheadCast
            _ < (c - C0) / 24 * secondOrderScale n +
                  c / 4 * secondOrderScale n :=
              add_lt_add_right hcapacityCast _
            _ = ((c - C0) / 24 + c / 4) * secondOrderScale n := by ring
            _ < c / 2 * secondOrderScale n :=
              mul_lt_mul_of_pos_right hcoeff hscale
        have hsumTail :
            (((p - 1) * (fixed.prod id).factorization p : ℕ) : ℝ) +
                (((p - 1) *
                  (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                    Nat.log2 (upperTailLength c n) + 1) : ℕ) : ℝ) <
              (upperTailLength c n : ℝ) := hsum.trans htailCast
        have hsumNat :
            (p - 1) * (fixed.prod id).factorization p +
                (p - 1) *
                  (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                    Nat.log2 (upperTailLength c n) + 1) ≤
              upperTailLength c n := by
          exact_mod_cast hsumTail.le
        have hcrossNat :
            (p - 1) *
                ((fixed.prod id).factorization p +
                  bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                  Nat.log2 (upperTailLength c n) + 1) ≤
              upperTailLength c n := by
          simpa only [Nat.add_assoc, Nat.mul_add] using hsumNat
        exact (Nat.mul_le_mul_left (p - 1)
          (by
            simpa only [Nat.add_assoc] using
              Nat.add_le_add_right hchargeBoundNat
                (Nat.log2 (upperTailLength c n) + 1))).trans hcrossNat
      simpa only [tail] using
        (centralTailProduct_factorization_ge_of_cross_capacity
          (n := n) hpPrime hchargeCost)
  have hhigh : ∀ p, p.Prime → yNat n < p →
      charge.factorization p ≤ tail.factorization p := by
    intro p hpPrime hpHigh
    simpa only [charge, fixed, tail] using
      bank.paperFixedExceptional_selectorTailCharge_factorization_le
        deltaStar hpHigh
  have hanchorCharge : divisor * charge ∣ tail :=
    mul_dvd_of_factorization_split hdivisorPos hchargePos htailPos
      hdivisorHigh hlow hhigh
  have hchargeDvd : charge ∣ certificate.prechargedTailTarget := by
    rw [GuardedCentralAnchorCertificate.prechargedTailTarget]
    exact (Nat.dvd_div_iff_mul_dvd certificate.divisor_dvd_tail).2
      (by simpa only [divisor, tail] using hanchorCharge)
  have hselectorIdentity :
      certificate.selectorTailTarget bank fixed * charge =
        certificate.prechargedTailTarget := by
    simpa only [charge] using
      certificate.selectorTailTarget_mul_selectorTailCharge
        bank fixed hchargeDvd
  have hcombinedRetained : ∀ p ∈ primesUpTo (2 * depth + 1),
      (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n + charge.factorization p ≤
        certificate.prechargedTailTarget.factorization p := by
    intro p hpSupport
    have hpPrime := (mem_primesUpTo.mp hpSupport).1
    have hpLow := (mem_primesUpTo.mp hpSupport).2.trans hsupportN
    have hpPredPosNat : 0 < p - 1 := Nat.sub_pos_of_lt hpPrime.one_lt
    have hpPredPos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpPredPosNat
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hpPredLe : (((p - 1 : ℕ) : ℝ)) ≤ (p : ℝ) := by
      exact_mod_cast Nat.sub_le p 1
    have hfixedP := hfixedChargeN bank p hpPrime hpLow
    have hfixedPred :
        ((fixed.prod id).factorization p : ℝ) ≤
          (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n := by
      have hinv : 1 / (p : ℝ) ≤
          1 / (((p - 1 : ℕ) : ℝ)) :=
        one_div_le_one_div_of_le hpPredPos hpPredLe
      calc
        ((fixed.prod id).factorization p : ℝ) ≤
            (c - C0) / 24 * secondOrderScale n / (p : ℝ) := by
          simpa only [fixed] using hfixedP
        _ = ((c - C0) / 24 * secondOrderScale n) *
              (1 / (p : ℝ)) := by ring
        _ ≤ ((c - C0) / 24 * secondOrderScale n) *
              (1 / (((p - 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hinv
            (mul_nonneg (by positivity) hscale.le)
        _ = (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
              secondOrderScale n := by
          field_simp [hpPredPos.ne']
    have htarget := hretainedTarget p hpSupport
    have hchargeCast : (charge.factorization p : ℝ) =
        ((fixed.prod id).factorization p : ℝ) +
          (bank.prechargeBaseStateProduct.factorization p : ℝ) := by
      exact_mod_cast hchargeFactorization p
    rw [hchargeCast]
    have htwice :
        (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n =
          2 * ((c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n) := by
      field_simp [hpPredPos.ne']
      ; ring
    rw [htwice] at htarget
    linarith
  refine ⟨bank, certificate, hanchorBank, hbaseDvd, ?_, ?_, ?_,
    htargetIdentity⟩
  · simpa only [charge, fixed] using hchargeDvd
  · intro p hpSupport
    simpa only [charge, fixed, Nat.cast_ofNat] using
      hcombinedRetained p hpSupport
  · simpa only [charge, fixed] using hselectorIdentity

/-! ## Tangent-compatible exponent after capacity -/



end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_010 := by
  exact @Erdos390.WholePaper.exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar
