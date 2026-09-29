-- Prove2me | solution 1 for mme_dwz_q5_actual_standard_products_asymptotic_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T14:11:42.829352+00:00
-- url     : https://prove2.me/submissions/caa3b01f-8084-479e-984d-c74c5091b8eb

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Theorems.Thm_mme_dwz_q5_actual_standard_products_of_numeric_budgets
import Theorems.Thm_mme_prime_half_range_salem_spencer_eps
import Theorems.Thm_mme_dwz_q5_target_count_log_rate
import Theorems.Thm_mme_dwz_q5_full_ambient_degree_entropy_bound
import Theorems.Thm_mme_dwz_q5_actual_Z_compatibility_log_rate
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Nat

open BigOperators Filter Real MME MME.TensorObj MME.StothersFourth
  MME.DWZRestrictedValue MME.CompleteSplit.CWFourth
  MME.DWZQ5ExactData MME.DWZFourthGlobalWitness MME.DWZQ5AsymptoticData
open scoped Classical Topology
universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace MME.DWZB2RateBudget

theorem ceil_exp_le (x : ℝ) (hx : 0 ≤ x) :
    (⌈Real.exp x⌉₊ : ℝ) ≤ 2 * Real.exp x := by
  have h := Nat.ceil_lt_add_one (Real.exp_pos x).le
  have he : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  linarith

theorem log_linear_div_tendsto (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ ↦ Real.log (a * (n : ℝ) + b) / (n : ℝ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hleft : Tendsto (fun n : ℕ ↦ Real.log a / (n : ℝ) +
      Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add hlog
  have hright : Tendsto (fun n : ℕ ↦ Real.log (a + b) / (n : ℝ) +
      Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add hlog
  apply hleft.squeeze' hright
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have h := Real.log_le_log (mul_pos ha hn0) (le_add_of_nonneg_right hb)
    rw [Real.log_mul ha.ne' hn0.ne'] at h
    simpa only [add_div] using div_le_div_of_nonneg_right h hn0.le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
    have hab : 0 < a + b := add_pos_of_pos_of_nonneg ha hb
    have h : a * (n : ℝ) + b ≤ (a + b) * (n : ℝ) := by nlinarith
    have hl := Real.log_le_log (by positivity : 0 < a * (n : ℝ) + b) h
    rw [Real.log_mul hab.ne' hn0.ne'] at hl
    simpa only [add_div] using div_le_div_of_nonneg_right hl hn0.le

theorem eventually_linear_le_exp (a b e : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, a * (n : ℝ) + b ≤ Real.exp (e * (n : ℝ)) := by
  have h := (log_linear_div_tendsto a b ha hb).eventually (gt_mem_nhds he)
  filter_upwards [h, eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hl : Real.log (a * (n : ℝ) + b) ≤ e * (n : ℝ) :=
    ((div_lt_iff₀ hnR).mp hn).le
  exact (Real.log_le_iff_le_exp (by positivity)).mp hl

theorem finite_copy_budget_of_exp_bounds
    (N p s T : ℕ) (a b rho delta : ℝ)
    (hp : 0 < p) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hpbound : (p : ℝ) ≤ Real.exp (b * (N : ℝ)))
    (hsbound : (p : ℝ) ^ (1 - delta) ≤ (s : ℝ))
    (hTbound : Real.exp (a * (N : ℝ)) ≤ (T : ℝ))
    (hloss : 16 * (3 * (N : ℝ) + 2) ≤
      Real.exp ((a - (rho + (1 + delta) * b)) * (N : ℝ))) :
    let r := ⌈Real.exp (rho * (N : ℝ))⌉₊
    Real.exp (rho * (N : ℝ)) ≤ (r : ℝ) ∧
      8 * p ^ 2 * (r * (3 * N + 2)) ≤ 3 * T * s := by
  dsimp only
  refine ⟨Nat.le_ceil _, ?_⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hfactor : (p : ℝ) ^ 2 ≤
      Real.exp (((1 + delta) * b) * (N : ℝ)) * (s : ℝ) := by
    have hb := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ p) hpbound
      (by linarith : 0 ≤ 1 + delta)
    rw [← Real.exp_mul] at hb
    have hid : (p : ℝ) ^ 2 = (p : ℝ) ^ (1 + delta) * (p : ℝ) ^ (1 - delta) := by
      rw [← Real.rpow_add hpR]
      norm_num
    rw [hid]
    calc
      (p : ℝ) ^ (1 + delta) * (p : ℝ) ^ (1 - delta) ≤
          Real.exp ((b * (N : ℝ)) * (1 + delta)) * (s : ℝ) :=
        mul_le_mul hb hsbound (Real.rpow_nonneg hpR.le _) (Real.exp_pos _).le
      _ = _ := by congr 2; ring
  have hr := ceil_exp_le (rho * (N : ℝ)) (mul_nonneg hrho (Nat.cast_nonneg _))
  have hmain : 8 * (p : ℝ) ^ 2 *
      ((⌈Real.exp (rho * (N : ℝ))⌉₊ : ℝ) * (3 * (N : ℝ) + 2)) ≤ (T : ℝ) * s := by
    calc
      _ ≤ 8 * (Real.exp (((1 + delta) * b) * (N : ℝ)) * (s : ℝ)) *
          ((2 * Real.exp (rho * (N : ℝ))) * (3 * (N : ℝ) + 2)) := by gcongr
      _ = (16 * (3 * (N : ℝ) + 2)) *
          Real.exp ((rho + (1 + delta) * b) * (N : ℝ)) * (s : ℝ) := by
        rw [add_mul rho ((1 + delta) * b) (N : ℝ), Real.exp_add]
        ring
      _ ≤ Real.exp ((a - (rho + (1 + delta) * b)) * (N : ℝ)) *
          Real.exp ((rho + (1 + delta) * b) * (N : ℝ)) * (s : ℝ) := by gcongr
      _ = Real.exp (a * (N : ℝ)) * (s : ℝ) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ ≤ (T : ℝ) * (s : ℝ) := by gcongr
  have hmain' : 8 * (p : ℝ) ^ 2 *
      ((⌈Real.exp (rho * (N : ℝ))⌉₊ : ℝ) * (3 * (N : ℝ) + 2)) ≤ 3 * (T : ℝ) * s := by
    nlinarith [mul_nonneg (Nat.cast_nonneg T : (0 : ℝ) ≤ T) (Nat.cast_nonneg s)]
  exact_mod_cast hmain'

theorem eventually_copy_budget_of_exp_bounds
    (a b rho delta : ℝ) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hgap : rho + (1 + delta) * b < a) :
    ∀ᶠ N : ℕ in atTop, ∀ p s T : ℕ,
      0 < p →
      (p : ℝ) ≤ Real.exp (b * (N : ℝ)) →
      (p : ℝ) ^ (1 - delta) ≤ (s : ℝ) →
      Real.exp (a * (N : ℝ)) ≤ (T : ℝ) →
      let r := ⌈Real.exp (rho * (N : ℝ))⌉₊
      Real.exp (rho * (N : ℝ)) ≤ (r : ℝ) ∧
        8 * p ^ 2 * (r * (3 * N + 2)) ≤ 3 * T * s := by
  have h := eventually_linear_le_exp 48 32 (a - (rho + (1 + delta) * b))
    (by norm_num) (by norm_num) (sub_pos.mpr hgap)
  filter_upwards [h] with N hN
  intro p s T hp hpbound hsbound hTbound
  apply finite_copy_budget_of_exp_bounds N p s T a b rho delta hp hrho hdelta
    hpbound hsbound hTbound
  nlinarith

end MME.DWZB2RateBudget

namespace MME.DWZB2Hash

theorem exp_nat_mul_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ Real.exp (a * (N : ℝ))) atTop atTop :=
  Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha)

/-- Exponential degree ceilings supply the modulus and the hashing set, with arbitrary
strict slack in the modulus exponent. -/
theorem prime_set_of_exponential_bounds (L b δ : ℝ)
    (hL : 0 ≤ L) (hLb : L < b) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ d W : ℕ,
      (d : ℝ) ≤ Real.exp (L * (N : ℝ)) →
      (W : ℝ) ≤ Real.exp (L * (N : ℝ)) →
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 < p ∧
        4 * d ≤ p ∧ 8 * W ≤ p ∧ (p : ℝ) ≤ Real.exp (b * (N : ℝ)) ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
          ThreeAPFree (S : Set ℕ) ∧ 0 < S.card ∧
          (p : ℝ) ^ (1 - δ) ≤ (S.card : ℝ) := by
  let k : ℝ := (L + b) / 2
  have hLk : L < k := by dsimp [k]; linarith
  have hkb : k < b := by dsimp [k]; linarith
  have hk : 0 < k := lt_of_le_of_lt hL hLk
  obtain ⟨B₀, hB₀⟩ := mme_prime_half_range_salem_spencer_eps δ hδ
  have hthreshold := (exp_nat_mul_tendsto k hk).eventually_ge_atTop (B₀ : ℝ)
  have hlower := (exp_nat_mul_tendsto (k - L) (sub_pos.mpr hLk)).eventually_ge_atTop 8
  have hupper := (exp_nat_mul_tendsto (b - k) (sub_pos.mpr hkb)).eventually_ge_atTop 4
  filter_upwards [hthreshold, hlower, hupper] with N hN hlo hup
  intro d W hd hW
  let B := ⌈Real.exp (k * (N : ℝ))⌉₊
  have hceil : Real.exp (k * (N : ℝ)) ≤ (B : ℝ) := Nat.le_ceil _
  have hB : B₀ ≤ B := by exact_mod_cast hN.trans hceil
  obtain ⟨p, hp, hpodd, hp8, hBp, hpB, S, hS, hfree, hcard, hsize⟩ := hB₀ B hB
  have hBreal : (B : ℝ) ≤ (p : ℝ) := by exact_mod_cast hBp.le
  have hlow : 8 * Real.exp (L * (N : ℝ)) ≤ (B : ℝ) := by
    calc
      _ ≤ Real.exp ((k - L) * (N : ℝ)) * Real.exp (L * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hlo (Real.exp_pos _).le
      _ = Real.exp (k * (N : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hceil
  have hfour : (4 * d : ℝ) ≤ (p : ℝ) := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith [hBreal]
  have height : (8 * W : ℝ) ≤ (p : ℝ) := by nlinarith [hBreal]
  have hBup : (B : ℝ) ≤ 2 * Real.exp (k * (N : ℝ)) := by
    have hc : (B : ℝ) < Real.exp (k * (N : ℝ)) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have he : 1 ≤ Real.exp (k * (N : ℝ)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hk.le (Nat.cast_nonneg _))
    linarith
  have hpup : (p : ℝ) ≤ Real.exp (b * (N : ℝ)) := by
    calc
      _ ≤ 2 * (B : ℝ) := by exact_mod_cast hpB
      _ ≤ 4 * Real.exp (k * (N : ℝ)) := by linarith
      _ ≤ Real.exp ((b - k) * (N : ℝ)) * Real.exp (k * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hup (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact ⟨p, hp, hpodd, hp8, by exact_mod_cast hfour, by exact_mod_cast height,
    hpup, S, hS, hfree, hcard, hsize⟩

end MME.DWZB2Hash

namespace MME.DWZB2Hash

/-- Pointwise, eventually uniform assembly of all three finite numeric budgets.
The target and degree exponents are chosen strictly within the available rate gap. -/
theorem eventually_uniform_budget_of_rate_gap (H L rho : ℝ)
    (hL : 0 ≤ L) (hrho : 0 ≤ rho) (hgap : rho < H - L) :
    ∃ a l : ℝ, a < H ∧ L < l ∧
      ∀ᶠ N : ℕ in atTop, ∀ d W T : ℕ,
        (d : ℝ) ≤ Real.exp (l * (N : ℝ)) →
        (W : ℝ) ≤ Real.exp (l * (N : ℝ)) →
        Real.exp (a * (N : ℝ)) ≤ (T : ℝ) →
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 < p ∧ 4 * d ≤ p ∧ 8 * W ≤ p ∧
          ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
            ThreeAPFree (S : Set ℕ) ∧ 0 < S.card ∧
            ∃ r : ℕ, Real.exp (rho * (N : ℝ)) ≤ (r : ℝ) ∧
              8 * p ^ 2 * (r * (3 * N + 2)) ≤ 3 * T * S.card := by
  let b := (L + (H - rho)) / 2
  let l := (L + b) / 2
  let a := (H + (rho + b)) / 2
  have hLb : L < b := by dsimp [b]; linarith
  have hbH : rho + b < H := by dsimp [b]; linarith
  have hb : 0 < b := lt_of_le_of_lt hL hLb
  have hLl : L < l := by dsimp [l]; linarith
  have hlb : l < b := by dsimp [l]; linarith
  have haH : a < H := by dsimp [a]; linarith
  have hba : rho + b < a := by dsimp [a]; linarith
  let δ := (a - (rho + b)) / (2 * b)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hba) (by positivity)
  have hδmul : δ * b = (a - (rho + b)) / 2 := by
    dsimp [δ]
    field_simp [hb.ne']
  have hbudgetGap : rho + (1 + δ) * b < a := by nlinarith
  have hhash := prime_set_of_exponential_bounds l b δ (le_trans hL hLl.le) hlb hδ
  have hbudget := MME.DWZB2RateBudget.eventually_copy_budget_of_exp_bounds
    a b rho δ hrho hδ.le hbudgetGap
  refine ⟨a, l, haH, hLl, ?_⟩
  filter_upwards [hhash, hbudget] with N hN hNbudget
  intro d W T hd hW hT
  obtain ⟨p, hp, hpodd, hp8, hpd, hpW, hpbound, S, hS, hfree, hcard, hsize⟩ :=
    hN d W hd hW
  have hcopy := hNbudget p S.card T hp.pos hpbound hsize hT
  exact ⟨p, hp, hpodd, hp8, hpd, hpW, S, hS, hfree, hcard,
    ⌈Real.exp (rho * (N : ℝ))⌉₊, hcopy.1, hcopy.2⟩

/-- Eventual target lower and degree upper rates imply all numeric budgets,
retaining every nonnegative copy exponent strictly below H-L. -/
theorem eventually_budget_of_rates (T d W : ℕ → ℕ) (H L rho : ℝ)
    (hL : 0 ≤ L) (hrho : 0 ≤ rho) (hgap : rho < H - L)
    (hT : ∀ a : ℝ, a < H → ∀ᶠ N : ℕ in atTop,
      Real.exp (a * (N : ℝ)) ≤ (T N : ℝ))
    (hD : ∀ l : ℝ, L < l → ∀ᶠ N : ℕ in atTop,
      (d N : ℝ) ≤ Real.exp (l * (N : ℝ)) ∧
      (W N : ℝ) ≤ Real.exp (l * (N : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 < p ∧ 4 * d N ≤ p ∧ 8 * W N ≤ p ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
          ThreeAPFree (S : Set ℕ) ∧ 0 < S.card ∧
          ∃ r : ℕ, Real.exp (rho * (N : ℝ)) ≤ (r : ℝ) ∧
            8 * p ^ 2 * (r * (3 * N + 2)) ≤ 3 * T N * S.card := by
  obtain ⟨a,l,ha,hl,hbudget⟩ := eventually_uniform_budget_of_rate_gap H L rho hL hrho hgap
  filter_upwards [hbudget, hT a ha, hD l hl] with N hN hNT hND
  exact hN (d N) (W N) (T N) hND.1 hND.2 hNT

end MME.DWZB2Hash

namespace MME.DWZB2Hash

/-- Every fixed polynomial factor is absorbed by any positive exponential slack. -/
theorem eventually_polynomial_le_exp (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((N : ℝ) + 1) ^ k ≤ Real.exp (ε * (N : ℝ)) := by
  have hlim : Tendsto (fun N : ℕ ↦ (k : ℝ) *
      (Real.log ((N : ℝ) + 1) / (N : ℝ))) atTop (𝓝 0) := by
    simpa only [one_mul, mul_zero] using
      (MME.DWZB2RateBudget.log_linear_div_tendsto 1 1
        (by norm_num) (by norm_num)).const_mul (k : ℝ)
  have h := hlim.eventually (gt_mem_nhds hε)
  filter_upwards [h, eventually_gt_atTop 0] with N hN hn
  have hnR : (0 : ℝ) < N := by exact_mod_cast hn
  apply (Real.log_le_iff_le_exp (by positivity : 0 < ((N : ℝ) + 1) ^ k)).mp
  rw [Real.log_pow]
  apply (div_lt_iff₀ hnR).mp _ |>.le
  simpa only [mul_div_assoc] using hN

/-- Polynomial-exponential upper bounds have every strictly larger exponential rate. -/
theorem eventually_polynomial_exp_bound (k : ℕ) (e l : ℝ) (hel : e < l) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℝ,
      d ≤ ((N : ℝ) + 1) ^ k * Real.exp (e * (N : ℝ)) →
      d ≤ Real.exp (l * (N : ℝ)) := by
  filter_upwards [eventually_polynomial_le_exp k (l - e) (sub_pos.mpr hel)] with N hN
  intro d hd
  calc
    d ≤ ((N : ℝ) + 1) ^ k * Real.exp (e * (N : ℝ)) := hd
    _ ≤ Real.exp ((l - e) * (N : ℝ)) * Real.exp (e * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
    _ = Real.exp (l * (N : ℝ)) := by rw [← Real.exp_add]; congr 1; ring

theorem eventually_degree45_exp_bound (e l : ℝ) (hel : e < l) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      (d : ℝ) ≤ ((N : ℝ) + 1) ^ 45 * Real.exp (e * (N : ℝ)) →
      (d : ℝ) ≤ Real.exp (l * (N : ℝ)) := by
  filter_upwards [eventually_polynomial_exp_bound 45 e l hel] with N hN
  intro d hd
  exact hN d hd

end MME.DWZB2Hash

namespace MME.DWZB2ActualExtraction

attribute [local irreducible] MME.DWZQ5ExactData.rawProfile
  MME.DWZQ5ExactData.component MME.DWZFourthGlobalWitness.coarseAddress

theorem shared_W_public (t : ℕ) :
    let D := ∏ c : Fin 45, (rawProfile c).denominator
    let m := fun c : Fin 45 ↦ component c * (D * t) / (rawProfile c).denominator
    let n := fun c : Fin 45 ↦ (rawProfile c).length (m c)
    let N := ∑ c : Fin 45, n c
    let shape : Fin 45 → Fin 3 → ℕ := fun c i ↦ (coarseAddress c i).val
    let z := fun c (l : Fin 5) ↦ (rawProfile c).count l * m c
    let mu : Fin 3 → Fin 45 → Fin 5 → ℕ := fun
      | 0, c, l => if shape c 1 = 0 then z c (Fin.rev l) else 0
      | 1, c, l => if shape c 0 = 0 then z c (Fin.rev l) else 0
      | 2, c, l => z c l
    let M : Fin 3 → ℕ → ℕ :=
      fun i g ↦ ∑ c : {c : Fin 45 // shape c i = g}, n c.val
    let Cell := {s : Fin 3 → Fin 9 // (∑ i, (s i).val) = 8}
    let tables : Finset (Cell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ s : {s : Cell // s.val i = g}, (h s.val).val) = M i g.val)
    let _degree := fun mode : Fin 3 ↦
      ∑ h ∈ tables, ∏ g : Fin 9, (M mode g.val).factorial /
        ∏ s : {s : Cell // s.val mode = g}, ((h s.val).val).factorial
    let coarse := fun c : Fin 45 ↦ coarseAddress c 2
    let boundary := fun c : Fin 45 ↦ shape c 0 = 0 ∨ shape c 1 = 0
    let F := fun i : Fin 9 × Fin 5 ↦
      ∑ c : {c : Fin 45 // coarse c = i.1}, mu 2 c.val i.2
    let pooled : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ := fun
      | (Sum.inl c, (g,l)) => if boundary c ∧ coarse c = g then mu 2 c l else 0
      | (Sum.inr g', (g,l)) => if g' = g then F (g,l) -
          ∑ c ∈ Finset.univ.filter (fun c ↦ boundary c ∧ coarse c = g), mu 2 c l
        else 0
    let collapse := fun c : Fin 45 ↦ if boundary c then Sum.inl c else Sum.inr (coarse c)
    let W :=
      (∏ i : Fin 9 × Fin 5, (F i).factorial /
        ∏ di : {di : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
          (pooled di.val).factorial) *
      (∏ d : Fin 45 ⊕ Fin 9, (∑ i, pooled (d,i)).factorial /
        ∏ c : {c : Fin 45 // collapse c = d}, (n c.val).factorial)
    MME.DWZQ5AsymptoticData.W t = W := by
  classical
  intro D m n N shape z mu M Cell tables _degree coarse boundary F pooled collapse W
  have hshape : MME.DWZQ5AsymptoticData.shape = shape := rfl
  have hcoarse : MME.DWZQ5AsymptoticData.coarse = coarse := rfl
  have hmu : MME.DWZQ5AsymptoticData.mu t = mu := by
    funext i c l
    fin_cases i <;> rfl
  have hF (i : Fin 9 × Fin 5) :
      MME.DWZQ5AsymptoticData.F t i = F i := by
    unfold MME.DWZQ5AsymptoticData.F
    rw [hmu, hcoarse]
  have hpool (i : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5)) :
      MME.DWZQ5AsymptoticData.pooled t i = pooled i := by
    rcases i with ⟨d,g,l⟩
    cases d with
    | inl c =>
      simp only [MME.DWZQ5AsymptoticData.pooled, pooled,
        MME.DWZQ5AsymptoticData.boundary, boundary, hmu, hshape, hcoarse]
    | inr g' =>
      simp only [MME.DWZQ5AsymptoticData.pooled, pooled,
        MME.DWZQ5AsymptoticData.boundary, boundary, hmu, hshape, hcoarse]
      split_ifs
      · apply congrArg₂ Nat.sub
        · exact hF (g,l)
        · apply Finset.sum_congr
          · ext c
            simp only [Finset.mem_filter, Finset.mem_univ]
          · intro c _
            rfl
      · rfl
  have hcollapse (c : Fin 45) :
      MME.DWZQ5AsymptoticData.collapse c = collapse c := by
    by_cases hb : boundary c
    · simp only [MME.DWZQ5AsymptoticData.collapse,
        MME.DWZQ5AsymptoticData.boundary, collapse, boundary, hshape, hcoarse] at *
    · simp only [MME.DWZQ5AsymptoticData.collapse,
        MME.DWZQ5AsymptoticData.boundary, collapse, boundary, hshape, hcoarse] at *
  unfold MME.DWZQ5AsymptoticData.W
  dsimp only [W]
  apply congrArg₂ Nat.mul
  · apply Finset.prod_congr rfl
    intro i _
    apply congrArg₂ Nat.div
    · exact congrArg Nat.factorial (hF i)
    · apply Finset.prod_congr
      · ext di
        simp only [Finset.mem_univ]
      · intro di _
        exact congrArg Nat.factorial (hpool di.val)
  · apply Finset.prod_congr rfl
    intro d _
    apply congrArg₂ Nat.div
    · apply congrArg Nat.factorial
      apply Finset.sum_congr rfl
      intro i _
      exact hpool (d,i)
    · let e : {c : Fin 45 // MME.DWZQ5AsymptoticData.collapse c = d} ≃
          {c : Fin 45 // collapse c = d} :=
        Equiv.subtypeEquivRight (fun c ↦ by rw [hcollapse c])
      exact Fintype.prod_equiv e _ _ (fun _ ↦ rfl)

theorem finite_restrict {K : Type u} [Field K] (t p r : ℕ) (ht : 0 < t)
    [Fact p.Prime] (S : Finset ℕ) (hS : S ⊆ Finset.range (p / 2))
    (hfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd p) (hp : 8 < p)
    (hxy : 4 * max (degree t 0) (degree t 1) ≤ p)
    (hz : 8 * (W t - 1) ≤ p)
    (hbudget : 8 * p ^ 2 * (r * (3 * N t + 2)) ≤ 3 * targetCount t * S.card) :
    TensorObj.Restrict
      (bigAdd (fun _ : Fin r ↦ kronFin 45 (fun c ↦ prescribedZPower
        (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
        (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
        (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
          cwSquarePairGrade 5 a.down.val.1)
        (rawProfile c) (m t c))))
      ((CWObj K 5).kronPow (N t * 4)) := by
  refine mme_dwz_q5_actual_standard_products_of_numeric_budgets (K := K)
    t p r ht S hS hfree hpodd hp hxy ?_ hbudget
  apply le_trans (Nat.mul_le_mul_left 8 (Nat.sub_le_sub_right (le_of_eq ?_) 1)) hz
  convert (shared_W_public t).symm using 1

end MME.DWZB2ActualExtraction

namespace MME.DWZB2TargetRate

theorem N_tendsto : Tendsto N atTop atTop :=
  mme_dwz_q5_target_count_log_rate.2.2.2.1

theorem target_eventually_lower (a : ℝ) (ha : a < targetRate) :
    ∀ᶠ t : ℕ in atTop, Real.exp (a * (N t : ℝ)) ≤ (targetCount t : ℝ) :=
  mme_dwz_q5_target_count_log_rate.2.2.2.2.2 a ha

end MME.DWZB2TargetRate

namespace MME.DWZB2AsymptoticExtraction

theorem from_actual_rates {K : Type u} [Field K]
    (hdegree : ∀ (t : ℕ), 0 < t → ∀ mode : Fin 3,
      (degree t mode : ℝ) ≤ ((N t : ℝ) + 1) ^ 45 *
        Real.exp ((N t : ℝ) * ((entropyUpper : ℝ) - marginalEntropy mode)))
    (hcompat : ∀ a : ℝ, compatibilityRate < a →
      ∀ᶠ t : ℕ in atTop, ((W t - 1 : ℕ) : ℝ) ≤ Real.exp (a * (N t : ℝ)))
    (rho : ℝ) (hrho : 0 ≤ rho) (hgap : rho < extractionRate) :
    ∀ᶠ t : ℕ in atTop, ∃ r : ℕ,
      Real.exp (rho * (N t : ℝ)) ≤ (r : ℝ) ∧
      TensorObj.Restrict
        (bigAdd (fun _ : Fin r ↦ kronFin 45 (fun c ↦ prescribedZPower
          (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
          (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
          (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
            cwSquarePairGrade 5 a.down.val.1)
          (rawProfile c) (m t c))))
        ((CWObj K 5).kronPow (N t * 4)) := by
  have hL : 0 ≤ hashRate := le_max_left _ _
  have hX : (entropyUpper : ℝ) - marginalEntropy 0 ≤ hashRate :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hY : (entropyUpper : ℝ) - marginalEntropy 1 ≤ hashRate :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hW : compatibilityRate ≤ hashRate :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨a,l,ha,hl,hbudget⟩ := MME.DWZB2Hash.eventually_uniform_budget_of_rate_gap
    targetRate hashRate rho hL hrho hgap
  have hupper (mode : Fin 3)
      (hmode : (entropyUpper : ℝ) - marginalEntropy mode < l) :
      ∀ᶠ t : ℕ in atTop, (degree t mode : ℝ) ≤ Real.exp (l * (N t : ℝ)) := by
    have hp := MME.DWZB2TargetRate.N_tendsto.eventually
      (MME.DWZB2Hash.eventually_degree45_exp_bound
        ((entropyUpper : ℝ) - marginalEntropy mode) l hmode)
    filter_upwards [hp, eventually_gt_atTop 0] with t ht ht0
    apply ht (degree t mode)
    simpa only [mul_comm ((N t : ℝ))] using hdegree t ht0 mode
  have hb := MME.DWZB2TargetRate.N_tendsto.eventually hbudget
  filter_upwards [hb, hupper 0 (lt_of_le_of_lt hX hl),
    hupper 1 (lt_of_le_of_lt hY hl), hcompat l (lt_of_le_of_lt hW hl),
    MME.DWZB2TargetRate.target_eventually_lower a ha, eventually_gt_atTop 0]
    with t hbt hXt hYt hWt hTt ht
  have hd : ((max (degree t 0) (degree t 1) : ℕ) : ℝ) ≤ Real.exp (l * (N t : ℝ)) := by
    rw [Nat.cast_max]
    exact max_le hXt hYt
  obtain ⟨p,hp,hodd,hp8,hxy,hz,S,hS,hfree,hcard,r,hr,hnum⟩ :=
    hbt (max (degree t 0) (degree t 1)) (W t - 1) (targetCount t) hd hWt hTt
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨r,hr,MME.DWZB2ActualExtraction.finite_restrict (K := K)
    t p r ht S hS hfree hodd hp8 hxy hz hnum⟩

end MME.DWZB2AsymptoticExtraction

theorem solution {K : Type u} [Field K]
    (rho : ℝ) (hrho : 0 ≤ rho) (hgap : rho < extractionRate) :
    ∀ᶠ t : ℕ in atTop, ∃ r : ℕ,
      Real.exp (rho * (N t : ℝ)) ≤ (r : ℝ) ∧
      TensorObj.Restrict
        (bigAdd (fun _ : Fin r ↦ kronFin 45 (fun c ↦ prescribedZPower
          (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
          (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
          (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
            cwSquarePairGrade 5 a.down.val.1)
          (rawProfile c) (m t c))))
        ((CWObj K 5).kronPow (N t * 4)) := by
  exact MME.DWZB2AsymptoticExtraction.from_actual_rates
    mme_dwz_q5_full_ambient_degree_entropy_bound
    mme_dwz_q5_actual_Z_compatibility_log_rate.2.2.2 rho hrho hgap
