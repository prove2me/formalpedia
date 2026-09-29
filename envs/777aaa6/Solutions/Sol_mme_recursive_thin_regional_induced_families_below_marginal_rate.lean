-- Prove2me | solution 1 for mme_recursive_thin_regional_induced_families_below_marginal_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T15:53:45.648515+00:00
-- url     : https://prove2.me/submissions/ff2d39bc-62d6-4cca-b340-3571f651bc31

import Theorems.Thm_mme_salem_spencer_eps_form
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Instances.Nat
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Theorems.Thm_mme_recursive_thin_split_marginal_joint_counts
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Theorems.Thm_mme_scaled_multinomial_log_rate
import Definitions.Def_mme_recursive_x_hash_families
import Theorems.Thm_mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
import Theorems.Thm_mme_dwz_asymmetric_hash_singleton_fiber_card
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_Z_pair_fiber_card_le
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label


open Real
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000

namespace MME.DWZB2Hash

/-- The half-range costs no fixed positive power of the modulus. -/
theorem half_range_set_eps (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ P₀ : ℕ, ∀ p : ℕ, P₀ ≤ p →
      ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧ (p : ℝ) ^ (1 - ε) ≤ (S.card : ℝ) := by
  obtain ⟨Q₀, hQ₀⟩ := mme_salem_spencer_eps_form (ε / 2) (by positivity)
  obtain ⟨L, hL⟩ := exists_nat_ge ((3 : ℝ) ^ (2 / ε))
  refine ⟨2 * max Q₀ (max L 1) + 2, ?_⟩
  intro p hp
  let Q := p / 2
  have hQQ : Q₀ ≤ Q := by dsimp [Q]; omega
  have hQL : L ≤ Q := by dsimp [Q]; omega
  have hQpos : 0 < Q := by dsimp [Q]; omega
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hpQ : (p : ℝ) ≤ 3 * (Q : ℝ) := by
    have hnat : p ≤ 3 * Q := by dsimp [Q]; omega
    exact_mod_cast hnat
  have hbase : (3 : ℝ) ^ (2 / ε) ≤ (Q : ℝ) :=
    hL.trans (by exact_mod_cast hQL)
  have hpower : (3 : ℝ) ≤ (Q : ℝ) ^ (ε / 2) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 3 ^ (2 / ε))
      hbase (by positivity : 0 ≤ ε / 2)
    have hexp : (2 / ε) * (ε / 2) = 1 := by field_simp [ne_of_gt hε]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hexp, Real.rpow_one] at h
    exact h
  obtain ⟨S, hS, hfree, hsize⟩ := hQ₀ Q hQQ
  refine ⟨S, hS, hfree, le_trans ?_ hsize⟩
  calc
    (p : ℝ) ^ (1 - ε) ≤ (3 * (Q : ℝ)) ^ (1 - ε) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hpQ (by linarith)
    _ = (3 : ℝ) ^ (1 - ε) * (Q : ℝ) ^ (1 - ε) :=
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ 3 * (Q : ℝ) ^ (1 - ε) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
          (show 1 - ε ≤ 1 by linarith)
    _ ≤ (Q : ℝ) ^ (ε / 2) * (Q : ℝ) ^ (1 - ε) :=
      mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (Q : ℝ) ^ (1 - ε / 2) := by
      rw [← Real.rpow_add hQreal]
      congr 1
      ring

/-- A prime of constant-factor size with a near-linear progression-free half-range set. -/
theorem prime_half_range_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 < p ∧ B < p ∧ p ≤ 2 * B ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
          ThreeAPFree (S : Set ℕ) ∧ 0 < S.card ∧
          (p : ℝ) ^ (1 - ε) ≤ (S.card : ℝ) := by
  let δ := min ε (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨P₀, hP₀⟩ := half_range_set_eps δ hδ hδ1
  refine ⟨max P₀ 8, ?_⟩
  intro B hB
  have hB8 : 8 ≤ B := le_trans (le_max_right _ _) hB
  obtain ⟨p, hp, hBp, hpB⟩ := Nat.exists_prime_lt_and_le_two_mul B (by omega)
  have hp8 : 8 < p := lt_of_le_of_lt hB8 hBp
  obtain ⟨S, hS, hfree, hsize⟩ := hP₀ p
    (le_trans (le_trans (le_max_left _ _) hB) hBp.le)
  have hsize' : (p : ℝ) ^ (1 - ε) ≤ (S.card : ℝ) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le)
      (by have := min_le_left ε (1 / 2 : ℝ); dsimp [δ]; linarith)) hsize
  have hcard : 0 < S.card := by
    have : (0 : ℝ) < S.card := lt_of_lt_of_le
      (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _) hsize'
    exact_mod_cast this
  exact ⟨p, hp, hp.odd_of_ne_two (by omega), hp8, hBp, hpB,
    S, hS, hfree, hcard, hsize'⟩

/-- Finite explicit counterpart, with the subexponential Behrend loss retained. -/
theorem prime_half_range_explicit (B : ℕ) (hB : 8 ≤ B) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 < p ∧ B < p ∧ p ≤ 2 * B ∧
      ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        ((p / 2 : ℕ) : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (p / 2 : ℕ))) ≤
          (S.card : ℝ) := by
  obtain ⟨p, hp, hBp, hpB⟩ := Nat.exists_prime_lt_and_le_two_mul B (by omega)
  obtain ⟨S, hS, hfree, hsize⟩ := mme_behrend_explicit_threeAP_free (p / 2)
  exact ⟨p, hp, hp.odd_of_ne_two (by omega), by omega, hBp, hpB, S, hS, hfree, hsize⟩

end MME.DWZB2Hash



open Filter Real
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 500000

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
  obtain ⟨B₀, hB₀⟩ := prime_half_range_eps δ hδ
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



open Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

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



open BigOperators Filter MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MME.DWZC1CoarseCounts

theorem prescribed_card {A : Type*} [Fintype A] (n : ℕ) (m : A → ℕ)
    (hm : ∑ a, m a = n) :
    Nat.card {w : Fin n → A // ∀ a, Fintype.card {t // w t = a} = m a} =
      Nat.multinomial Finset.univ m := by
  have h := mme_fintype_prescribed_fiber_function_card (α := Fin n) m
    (by simpa only [Fintype.card_fin] using hm)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.multinomial, hm] using h

theorem joint_card (half : ℕ) (parent : Fin 3 → ℕ) (n : ℕ)
    (m : Split half parent → ℕ) (hm : ∑ a, m a = n) :
    Nat.card {w : Fin n → Split half parent // HasJointCounts w m} =
      Nat.multinomial Finset.univ m := by
  have h := prescribed_card n m hm
  simpa only [HasJointCounts, count, Fintype.card_subtype] using h

theorem target_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) :
    (target (n := n) m).card = ∏ r, Nat.multinomial Finset.univ (m r) := by
  have he := @Equiv.subtypePiEquivPi (Fin R)
    (fun r ↦ Fin (n r) → Split half (parent r))
    (fun r w ↦ HasJointCounts w (m r))
  have hc := Nat.card_congr he
  rw [Nat.card_pi] at hc
  have hcard : (target (n := n) m).card =
      Nat.card {w : Address half R parent n // ∀ r, HasJointCounts (w r) (m r)} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, target]
  rw [hcard, hc]
  exact Finset.prod_congr rfl (fun r _ ↦ joint_card half (parent r) (n r) (m r) (hm r))

def marginal {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) (j : Fin (half + 1)) : ℕ :=
  ∑ a : {a : Split half parent // a.val i = j}, m a.val

theorem marginal_sum {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) :
    (∑ j, marginal m i j) = ∑ a, m a := by
  exact Fintype.sum_fiberwise (fun a : Split half parent ↦ a.val i) m

def degree {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) : ℕ :=
  ∏ j, (marginal m i j).factorial /
    ∏ a : {a : Split half parent // a.val i = j}, (m a.val).factorial

theorem joint_fiber_card (half : ℕ) (parent : Fin 3 → ℕ) (n : ℕ)
    (m : Split half parent → ℕ) (i : Fin 3) (x : Fin n → Fin (half + 1))
    (hx : ∀ j, Fintype.card {t // x t = j} = marginal m i j) :
    Nat.card {w : Fin n → Split half parent //
      HasJointCounts w m ∧ (∀ t, (w t).val i = x t)} = degree m i := by
  have h := mme_fintype_constrained_prescribed_fiber_function_card
    x (fun a : Split half parent ↦ a.val i) m (fun j ↦ (hx j).symm)
  have he : {w : Fin n → Split half parent //
      HasJointCounts w m ∧ (∀ t, (w t).val i = x t)} ≃
      {w : Fin n → Split half parent //
        (∀ t, (w t).val i = x t) ∧
          ∀ a, Fintype.card {t // w t = a} = m a} :=
    Equiv.subtypeEquivRight (fun w ↦ by
      simp only [HasJointCounts, count, Fintype.card_subtype, and_comm])
  rw [Nat.card_congr he, h]
  simp only [hx, degree]

theorem target_fiber_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (i : Fin 3) (x : ∀ r, Fin (n r) → Fin (half + 1))
    (hx : ∀ r j, Fintype.card {t // x r t = j} = marginal (m r) i j) :
    ((target (n := n) m).filter (fun w ↦ block i w = x)).card =
      ∏ r, degree (m r) i := by
  let W := {w : Address half R parent n //
    ∀ r, HasJointCounts (w r) (m r) ∧ ∀ t, (w r t).val i = x r t}
  have hc : ((target (n := n) m).filter (fun w ↦ block i w = x)).card = Nat.card W := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, target,
      Finset.filter_filter, W]
    apply congrArg Finset.card
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, hxw⟩ r
      exact ⟨hw r, fun t ↦ congrFun (congrFun hxw r) t⟩
    · intro hw
      exact ⟨fun r ↦ (hw r).1, funext fun r ↦ funext (hw r).2⟩
  have he := @Equiv.subtypePiEquivPi (Fin R)
    (fun r ↦ Fin (n r) → Split half (parent r))
    (fun r w ↦ HasJointCounts w (m r) ∧ ∀ t, (w t).val i = x r t)
  rw [hc, Nat.card_congr he, Nat.card_pi]
  exact Finset.prod_congr rfl (fun r _ ↦
    joint_fiber_card half (parent r) (n r) (m r) i (x r) (hx r))

theorem ambient_fiber_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (i : Fin 3) (a : Address half R parent n) (ha : a ∈ ambient (n := n) m) :
    ((ambient (n := n) m).filter (fun b ↦ block i b = block i a)).card =
      ∏ r, degree (m r) i := by
  have he := (mme_recursive_x_hash_family_counts half R parent n m).2.2 hthin
  rw [he]
  apply target_fiber_card
  intro r j
  have h := (Finset.mem_filter.mp ha).2 r i j
  simpa only [HasMarginalCounts, count, Fintype.card_subtype, block, marginal] using h

theorem degree_pos {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) : 0 < degree m i := by
  apply Finset.prod_pos
  intro j _
  exact Nat.multinomial_pos Finset.univ (fun a : {a : Split half parent // a.val i = j} ↦ m a.val)

theorem degree_factorial_spec {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) :
    (∏ a, (m a).factorial) * degree m i = ∏ j, (marginal m i j).factorial := by
  calc
    _ = (∏ j, ∏ a : {a : Split half parent // a.val i = j}, (m a.val).factorial) *
        (∏ j, (marginal m i j).factorial /
          ∏ a : {a : Split half parent // a.val i = j}, (m a.val).factorial) := by
      rw [Fintype.prod_fiberwise (fun a : Split half parent ↦ a.val i)
        (fun a ↦ (m a).factorial)]
      rfl
    _ = ∏ j, (∏ a : {a : Split half parent // a.val i = j}, (m a.val).factorial) *
        ((marginal m i j).factorial /
          ∏ a : {a : Split half parent // a.val i = j}, (m a.val).factorial) :=
      Finset.prod_mul_distrib.symm
    _ = ∏ j, (marginal m i j).factorial := by
      apply Finset.prod_congr rfl
      intro j _
      exact Nat.mul_div_cancel' (Nat.prod_factorial_dvd_factorial_sum Finset.univ
        (fun a : {a : Split half parent // a.val i = j} ↦ m a.val))

theorem multinomial_eq_marginal_mul_degree {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) :
    Nat.multinomial Finset.univ m =
      Nat.multinomial Finset.univ (marginal m i) * degree m i := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.prod_factorial_pos Finset.univ m)
  rw [Nat.multinomial_spec]
  calc
    (∑ a, m a).factorial = (∏ j, (marginal m i j).factorial) *
        Nat.multinomial Finset.univ (marginal m i) := by
      rw [Nat.multinomial_spec, marginal_sum]
    _ = (∏ a, (m a).factorial) *
        (Nat.multinomial Finset.univ (marginal m i) * degree m i) := by
      rw [← degree_factorial_spec]
      ring

theorem regional_multinomial_factorization (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) :
    (∏ r, Nat.multinomial Finset.univ (m r)) =
      (∏ r, Nat.multinomial Finset.univ (marginal (m r) i)) * ∏ r, degree (m r) i := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun r _ ↦ multinomial_eq_marginal_mul_degree (m r) i)

theorem ambient_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) :
    (ambient (n := n) m).card = ∏ r, Nat.multinomial Finset.univ (m r) := by
  rw [(mme_recursive_x_hash_family_counts half R parent n m).2.2 hthin]
  exact target_card half R parent n m hm

theorem ambient_image_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) (i : Fin 3) :
    ((ambient (n := n) m).image (block i)).card =
      ∏ r, Nat.multinomial Finset.univ (marginal (m r) i) := by
  have hc := Finset.card_eq_sum_card_image (block i) (ambient (n := n) m)
  have hf : (∑ x ∈ (ambient (n := n) m).image (block i),
      ((ambient (n := n) m).filter (fun w ↦ block i w = x)).card) =
      ((ambient (n := n) m).image (block i)).card * ∏ r, degree (m r) i := by
    calc
      _ = ∑ _x ∈ (ambient (n := n) m).image (block i), ∏ r, degree (m r) i := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact ambient_fiber_card half R parent hthin n m i a ha
      _ = _ := by simp
  rw [hf, ambient_card half R parent hthin n m hm,
    regional_multinomial_factorization half R parent m i] at hc
  exact (Nat.eq_of_mul_eq_mul_right
    (Finset.prod_pos (fun r _ ↦ degree_pos (m r) i)) hc).symm

end MME.DWZC1CoarseCounts



open BigOperators Filter MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MME.DWZC1CoarseCounts

noncomputable def entropyMass {A : Type*} [Fintype A] (m : A → ℕ) : ℝ :=
  ((∑ a, m a : ℕ) : ℝ) * Real.log ((∑ a, m a : ℕ) : ℝ) -
    ∑ a, (m a : ℝ) * Real.log (m a : ℝ)

def scaled {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (t : ℕ) (r : Fin R)
    (a : Split half (parent r)) : ℕ := m r a * t

def jointCount {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) : ℕ :=
  ∏ r, Nat.multinomial Finset.univ (m r)

def blockCount {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) : ℕ :=
  ∏ r, Nat.multinomial Finset.univ (marginal (m r) i)

def starDegree {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) : ℕ := ∏ r, degree (m r) i

noncomputable def jointEntropy {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) : ℝ := ∑ r, entropyMass (m r)

noncomputable def blockEntropy {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) : ℝ :=
  ∑ r, entropyMass (marginal (m r) i)

theorem jointCount_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) : 0 < jointCount m :=
  Finset.prod_pos (fun _r _ ↦ Nat.multinomial_pos _ _)

theorem blockCount_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) : 0 < blockCount m i :=
  Finset.prod_pos (fun _r _ ↦ Nat.multinomial_pos _ _)

theorem starDegree_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) : 0 < starDegree m i :=
  Finset.prod_pos (fun r _ ↦ degree_pos (m r) i)

theorem jointCount_eq_blockCount_mul_starDegree
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) :
    jointCount m = blockCount m i * starDegree m i :=
  regional_multinomial_factorization half R parent m i

theorem product_scaled_multinomial_rate
    {S : Type*} [Fintype S] {A : S → Type*} [∀ s, Fintype (A s)]
    (m : ∀ s, A s → ℕ) :
    Tendsto (fun t : ℕ ↦ Real.log
      (∏ s, (Nat.multinomial Finset.univ (fun a ↦ m s a * t) : ℝ)) / (t : ℝ))
      atTop (𝓝 (∑ s, entropyMass (m s))) := by
  have h := tendsto_finset_sum Finset.univ
    (fun s _ ↦ mme_scaled_multinomial_log_rate (m s))
  convert h using 1
  funext t
  rw [Real.log_prod]
  · exact Finset.sum_div ..
  · intro s _
    exact_mod_cast (Nat.multinomial_pos (s := Finset.univ)
      (f := fun a ↦ m s a * t)).ne'

theorem marginal_scaled {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (t : ℕ) (r : Fin R) (i : Fin 3)
    (j : Fin (half + 1)) :
    marginal (scaled m t r) i j = marginal (m r) i j * t := by
  simp only [marginal, scaled, Finset.sum_mul]

theorem jointCount_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) :
    Tendsto (fun t : ℕ ↦ Real.log (jointCount (scaled m t) : ℝ) / (t : ℝ))
      atTop (𝓝 (jointEntropy m)) := by
  simpa only [jointCount, scaled, Nat.cast_prod, jointEntropy] using
    product_scaled_multinomial_rate m

theorem blockCount_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) :
    Tendsto (fun t : ℕ ↦ Real.log (blockCount (scaled m t) i : ℝ) / (t : ℝ))
      atTop (𝓝 (blockEntropy m i)) := by
  have h := product_scaled_multinomial_rate (fun r ↦ marginal (m r) i)
  simpa only [blockCount, Nat.cast_prod, blockEntropy,
    show ∀ t r, marginal (scaled m t r) i = fun j ↦ marginal (m r) i j * t from
      fun t r ↦ funext (marginal_scaled m t r i)] using h

theorem starDegree_log_eq {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) :
    Real.log (starDegree m i : ℝ) =
      Real.log (jointCount m : ℝ) - Real.log (blockCount m i : ℝ) := by
  have h := jointCount_eq_blockCount_mul_starDegree m i
  have hb : (blockCount m i : ℝ) ≠ 0 := by exact_mod_cast (blockCount_pos m i).ne'
  have hd : (starDegree m i : ℝ) ≠ 0 := by exact_mod_cast (starDegree_pos m i).ne'
  rw [h, Nat.cast_mul, Real.log_mul hb hd]
  ring

theorem starDegree_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) :
    Tendsto (fun t : ℕ ↦ Real.log (starDegree (scaled m t) i : ℝ) / (t : ℝ))
      atTop (𝓝 (jointEntropy m - blockEntropy m i)) := by
  simpa only [starDegree_log_eq, sub_div] using
    (jointCount_log_rate m).sub (blockCount_log_rate m i)

def maxStarDegree {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) : ℕ :=
  max (max (starDegree m 0) (starDegree m 1)) (starDegree m 2)

private theorem log_max_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (max a b) = max (Real.log a) (Real.log b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.log_le_log ha h)]
  · rw [max_eq_left h, max_eq_left (Real.log_le_log hb h)]

theorem maxStarDegree_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) :
    Tendsto (fun t : ℕ ↦ Real.log (maxStarDegree (scaled m t) : ℝ) / (t : ℝ))
      atTop (𝓝 (max (max (jointEntropy m - blockEntropy m 0)
        (jointEntropy m - blockEntropy m 1)) (jointEntropy m - blockEntropy m 2))) := by
  have h := ((starDegree_log_rate m 0).max (starDegree_log_rate m 1)).max
    (starDegree_log_rate m 2)
  convert h using 1
  funext t
  have hd (i : Fin 3) : (0 : ℝ) < starDegree (scaled m t) i := by
    exact_mod_cast starDegree_pos (scaled m t) i
  rw [maxStarDegree, Nat.cast_max, Nat.cast_max,
    log_max_pos _ _ (lt_max_of_lt_left (hd 0)) (hd 2),
    log_max_pos _ _ (hd 0) (hd 1),
    max_div_div_right (Nat.cast_nonneg t), max_div_div_right (Nat.cast_nonneg t)]

theorem classical_surviving_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) :
    Tendsto (fun t : ℕ ↦
      (Real.log (jointCount (scaled m t) : ℝ) -
        Real.log (maxStarDegree (scaled m t) : ℝ)) / (t : ℝ))
      atTop (𝓝 (min (min (blockEntropy m 0) (blockEntropy m 1)) (blockEntropy m 2))) := by
  have h := (jointCount_log_rate m).sub (maxStarDegree_log_rate m)
  have hid : jointEntropy m -
      max (max (jointEntropy m - blockEntropy m 0) (jointEntropy m - blockEntropy m 1))
        (jointEntropy m - blockEntropy m 2) =
      min (min (blockEntropy m 0) (blockEntropy m 1)) (blockEntropy m 2) := by
    simp only [max_def, min_def]
    split_ifs <;> linarith
  simpa only [← sub_div, hid] using h

end MME.DWZC1CoarseCounts



open BigOperators MME MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace MME.DWZC1CoarseIsolation

-- The modular encoding lemmas follow the accepted regional X-isolation
-- construction; this file supplies simultaneous isolation in all three modes.
theorem field_support {half R N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (w : Address half R parent n) (t : Fin (N + 1)) :
    fieldWord p e 0 w t + fieldWord p e 1 w t + fieldWord p e 2 w t = (half : ZMod p) := by
  have h := (w (e t).1 (e t).2).property.1
  change (((w (e t).1 (e t).2).val 0).val : ZMod p) +
      (((w (e t).1 (e t).2).val 1).val : ZMod p) +
      (((w (e t).1 (e t).2).val 2).val : ZMod p) = _
  simpa only [Nat.cast_add] using congrArg (fun a : ℕ ↦ (a : ZMod p)) h

theorem field_eq_iff {half R N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (hp : half < p)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (i : Fin 3) (u v : Address half R parent n) :
    fieldWord p e i u = fieldWord p e i v ↔ block i u = block i v := by
  constructor
  · intro h
    funext r t
    obtain ⟨s, hs⟩ := e.surjective ⟨r,t⟩
    have ht := congrFun h s
    change ((block i u (e s).1 (e s).2).val : ZMod p) =
      ((block i v (e s).1 (e s).2).val : ZMod p) at ht
    rw [hs] at ht
    have hv := congrArg ZMod.val ht
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext hv
  · intro h
    funext t
    simp only [fieldWord, h]

theorem two_modes_injective {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (u v : Address half R parent n)
    (i j : Fin 3) (hij : i ≠ j)
    (hi : block i u = block i v) (hj : block j u = block j v) : u = v := by
  funext r t
  apply Subtype.ext
  have h0 := congrArg Fin.val (congrFun (congrFun hi r) t)
  have h1 := congrArg Fin.val (congrFun (congrFun hj r) t)
  have hu := (u r t).property.1
  have hv := (v r t).property.1
  change ((u r t).val i).val = ((v r t).val i).val at h0
  change ((u r t).val j).val = ((v r t).val j).val at h1
  funext k
  apply Fin.ext
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> omega

def SupportedMix {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (x y z : Address half R parent n) : Prop :=
  ∀ r t, ((x r t).val 0).val + ((y r t).val 1).val + ((z r t).val 2).val = half

def mixAddress {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (x y z : Address half R parent n) (h : SupportedMix x y z) :
    Address half R parent n := fun r t ↦
  ⟨![(x r t).val 0, (y r t).val 1, (z r t).val 2], h r t, by
    intro i
    fin_cases i
    · exact (x r t).property.2 0
    · exact (y r t).property.2 1
    · exact (z r t).property.2 2⟩

theorem mix_blocks {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (x y z : Address half R parent n) (h : SupportedMix x y z) :
    block 0 (mixAddress x y z h) = block 0 x ∧
    block 1 (mixAddress x y z h) = block 1 y ∧
    block 2 (mixAddress x y z h) = block 2 z := ⟨rfl, rfl, rfl⟩

theorem target_subset_ambient {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, Split half (parent r) → ℕ) :
    target (n := n) m ⊆ ambient m := by
  exact (mme_recursive_x_hash_family_counts half R parent n m).1

theorem mix_ambient {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, Split half (parent r) → ℕ)
    (x y z : Address half R parent n) (hx : x ∈ ambient m)
    (hy : y ∈ ambient m) (hz : z ∈ ambient m) (h : SupportedMix x y z) :
    mixAddress x y z h ∈ ambient m := by
  simp only [ambient, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz ⊢
  intro r i a
  fin_cases i
  · exact hx r 0 a
  · exact hy r 1 a
  · exact hz r 2 a

theorem finite_three_mode_isolation (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    {N p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hgrade : half < p)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (D : ℕ)
    (hdegree : ∀ i : Fin 3, ∀ a ∈ target (n := n) m,
      ((ambient m).filter (fun b ↦ block i b = block i a)).card ≤ D)
    (hlabels : 6 * D ≤ S.card) :
    ∃ q : (Fin (N + 2) → ZMod p) × ZMod p,
      ∃ kept : Finset (Address half R parent n),
        kept ⊆ (target m).filter (fun a ↦
          a ∈ bucketed m e (S.image (fun j : ℕ ↦ (j : ZMod p))) q) ∧
        (∀ i : Fin 3, Function.Injective (fun a : kept ↦ block i a.val)) ∧
        (∀ x y z : kept, SupportedMix x.val y.val z.val → x = y ∧ y = z) ∧
        (target (n := n) m).card * (S.card : ℝ) / (2 * (p : ℝ)^2) ≤
          (kept.card : ℝ) := by
  classical
  let A := ambient (n := n) m
  let T := target (n := n) m
  let castS := S.image (fun a : ℕ ↦ (a : ZMod p))
  let E := hashed m e castS
  let Ω := (Fin (N + 2) → ZMod p) × ZMod p
  have hTA : T ⊆ A := target_subset_ambient m
  have hcast : castS.card = S.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have ha' : a < p := (Finset.mem_range.mp (hSrange ha)).trans_le (Nat.div_le_self _ _)
    have hb' : b < p := (Finset.mem_range.mp (hSrange hb)).trans_le (Nat.div_le_self _ _)
    have hv := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hv
  have hSle : castS.card ≤ p := by
    calc castS.card = S.card := hcast
         _ ≤ (Finset.range (p / 2)).card := Finset.card_le_card hSrange
         _ ≤ p := by simp [Nat.div_le_self]
  have hbucket (q) : E q = bucketed m e castS q := by
    ext w
    simp only [E, hashed, bucketed, Finset.mem_filter]
    have hh := mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label hpodd S hSrange hSfree
      (half : ZMod p) (fieldWord p e 0 w) (fieldWord p e 1 w) (fieldWord p e 2 w)
      (field_support e w) q
    exact and_congr_right (fun _ ↦ hh.symm)
  have hsingle (w) (hw : w ∈ T) :
      (Finset.univ.filter (fun q : Ω ↦ w ∈ E q)).card = castS.card * p ^ (N + 1) := by
    have hwA : w ∈ ambient (n := n) m := hTA hw
    simpa only [E, hashed, Finset.mem_filter, hwA, true_and,
      dwzAsymmetricAffineStatesRetaining] using
      mme_dwz_asymmetric_hash_singleton_fiber_card hpodd (half : ZMod p) castS
        (fieldWord p e 0 w) (fieldWord p e 1 w) (fieldWord p e 2 w) (field_support e w)
  have hpair : ∀ pair ∈ (T ×ˢ A).filter (fun pair ↦ pair.1 ≠ pair.2 ∧
      ∃ i : Fin 3, block i pair.1 = block i pair.2),
      (Finset.univ.filter (fun q : Ω ↦ pair.1 ∈ E q ∧ pair.2 ∈ E q)).card ≤ p ^ (N + 1) := by
    intro pair hp
    obtain ⟨⟨haT, hbA⟩, hab, i, hi⟩ := by simpa using hp
    have haA : pair.1 ∈ ambient (n := n) m := hTA haT
    change pair.2 ∈ ambient (n := n) m at hbA
    have heq : (Finset.univ.filter (fun q : Ω ↦ pair.1 ∈ E q ∧ pair.2 ∈ E q)) =
        dwzAsymmetricAffineStatesRetaining (half : ZMod p) castS
          (fieldWord p e 0 pair.1) (fieldWord p e 1 pair.1) (fieldWord p e 2 pair.1) ∩
        dwzAsymmetricAffineStatesRetaining (half : ZMod p) castS
          (fieldWord p e 0 pair.2) (fieldWord p e 1 pair.2) (fieldWord p e 2 pair.2) := by
      ext q
      simp [E, hashed, haA, hbA, dwzAsymmetricAffineStatesRetaining]
    rw [heq]
    apply le_trans (b := castS.card * p ^ N)
    · have hneq (j : Fin 3) (hj : i ≠ j) : fieldWord p e j pair.1 ≠ fieldWord p e j pair.2 := by
        intro h
        exact hab (two_modes_injective _ _ i j hj hi ((field_eq_iff hgrade e j _ _).mp h))
      have hsame := (field_eq_iff hgrade e i _ _).mpr hi
      fin_cases i
      · exact mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le (half : ZMod p) castS
          _ _ _ _ _ _ (Or.inl ⟨hsame, hneq 1 (by decide)⟩)
      · exact mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le (half : ZMod p) castS
          _ _ _ _ _ _ (Or.inr ⟨hsame, hneq 0 (by decide)⟩)
      · change fieldWord p e 2 pair.1 = fieldWord p e 2 pair.2 at hsame
        rw [← hsame]
        exact mme_dwz_asymmetric_hash_shared_Z_pair_fiber_card_le (half : ZMod p) castS
          _ _ _ _ _ (hneq 0 (by decide))
    · simpa [pow_succ, mul_comm] using Nat.mul_le_mul_right (p ^ N) hSle
  have hclosure (q : Ω) (x : Address half R parent n) (hx : x ∈ T.filter (fun w ↦ w ∈ E q))
      (y) (hy : y ∈ T.filter (fun w ↦ w ∈ E q))
      (z) (hz : z ∈ T.filter (fun w ↦ w ∈ E q)) (h : SupportedMix x y z) :
      ∃ w ∈ A.filter (fun a ↦ a ∈ E q),
        block 0 w = block 0 x ∧ block 1 w = block 1 y ∧ block 2 w = block 2 z := by
    refine ⟨mixAddress x y z h, ?_, mix_blocks x y z h⟩
    have hxA := hTA (Finset.mem_filter.mp hx).1
    have hyA := hTA (Finset.mem_filter.mp hy).1
    have hzA := hTA (Finset.mem_filter.mp hz).1
    have hmA := mix_ambient m x y z hxA hyA hzA h
    apply Finset.mem_filter.mpr
    refine ⟨hmA, ?_⟩
    rw [hbucket]
    have hxB := (hbucket q) ▸ (Finset.mem_filter.mp hx).2
    have hyB := (hbucket q) ▸ (Finset.mem_filter.mp hy).2
    have hzB := (hbucket q) ▸ (Finset.mem_filter.mp hz).2
    simp only [bucketed, Finset.mem_filter] at hxB hyB hzB ⊢
    exact ⟨hmA, hxB.2.1, hyB.2.2.1, hzB.2.2.2⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hlabelsR : 6 * (D : ℝ) ≤ castS.card := by rw [hcast]; exact_mod_cast hlabels
  have hmargin : ((p^2 : ℕ) : ℝ) * ((castS.card : ℝ) / (2 * (p : ℝ)^2)) +
      3 * (1 : ℕ) * (D : ℝ) ≤ (1 : ℕ) * (castS.card : ℝ) := by
    push_cast
    have heq : (p : ℝ)^2 * ((castS.card : ℝ) / (2 * (p : ℝ)^2)) = castS.card / 2 := by
      field_simp
    rw [heq]
    linarith
  obtain ⟨q, kept, hkept, hinj, hinduced, hsize⟩ :=
    mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
      block SupportedMix A T (fun q a ↦ a ∈ E q)
      (p^2) castS.card (p^(N+1)) D 1 (T.card : ℝ)
      ((castS.card : ℝ) / (2 * (p : ℝ)^2)) (by positivity)
      (by simp [pow_succ]; ring)
      (by simp) hdegree hsingle (by
        intro ab hab
        have hh := hpair ab hab
        convert hh using 1
        congr 1
        ext q
        simp) hTA hclosure hmargin
  refine ⟨q, kept, ?_, hinj, hinduced, ?_⟩
  · simpa only [hbucket q] using hkept
  · simpa only [hcast, T, mul_div_assoc] using hsize

end MME.DWZC1CoarseIsolation



open Filter Real
open scoped Topology Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

namespace MME.DWZC1CoarseHashRate

/-- A near-linear AP-free set can itself dominate every collision degree,
not merely fit inside a prime larger than that degree. -/
theorem eventually_prime_labels (L k b δ : ℝ)
    (hk : 0 < k) (hkb : k < b) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgap : L < (1 - δ) * k) :
    ∀ᶠ t : ℕ in atTop, ∀ D : ℕ,
      (D : ℝ) ≤ Real.exp (L * (t : ℝ)) →
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 < p ∧
        (p : ℝ) ≤ Real.exp (b * (t : ℝ)) ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
          ThreeAPFree (S : Set ℕ) ∧ 0 < S.card ∧ 6 * D ≤ S.card ∧
          (p : ℝ) ^ (1 - δ) ≤ (S.card : ℝ) := by
  obtain ⟨B₀, hB₀⟩ := MME.DWZB2Hash.prime_half_range_eps δ hδ
  have hthreshold := (MME.DWZB2Hash.exp_nat_mul_tendsto k hk).eventually_ge_atTop (B₀ : ℝ)
  have hupper := (MME.DWZB2Hash.exp_nat_mul_tendsto (b-k) (sub_pos.mpr hkb)).eventually_ge_atTop 4
  have hlabels := (MME.DWZB2Hash.exp_nat_mul_tendsto ((1-δ)*k-L)
    (sub_pos.mpr hgap)).eventually_ge_atTop 6
  filter_upwards [hthreshold, hupper, hlabels] with t ht hu hl
  intro D hD
  let B := ⌈Real.exp (k * (t : ℝ))⌉₊
  have hc : Real.exp (k * (t : ℝ)) ≤ (B : ℝ) := Nat.le_ceil _
  have hB : B₀ ≤ B := by exact_mod_cast ht.trans hc
  obtain ⟨p, hp, hpodd, hp8, hBp, hpB, S, hS, hfree, hcard, hsize⟩ := hB₀ B hB
  have hlow : Real.exp (k * (t : ℝ)) ≤ (p : ℝ) :=
    hc.trans (by exact_mod_cast hBp.le)
  have hBup : (B : ℝ) ≤ 2 * Real.exp (k * (t : ℝ)) := by
    have hceil : (B : ℝ) < Real.exp (k * (t : ℝ)) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have he : 1 ≤ Real.exp (k * (t : ℝ)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hk.le (Nat.cast_nonneg _))
    linarith
  have hpup : (p : ℝ) ≤ Real.exp (b * (t : ℝ)) := by
    calc
      _ ≤ 2 * (B : ℝ) := by exact_mod_cast hpB
      _ ≤ 4 * Real.exp (k * (t : ℝ)) := by linarith
      _ ≤ Real.exp ((b-k) * (t : ℝ)) * Real.exp (k * (t : ℝ)) :=
        mul_le_mul_of_nonneg_right hu (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hSexp : Real.exp (((1-δ)*k) * (t : ℝ)) ≤ (S.card : ℝ) := by
    have he := Real.rpow_le_rpow (Real.exp_pos _).le hlow (by linarith : 0 ≤ 1-δ)
    rw [← Real.exp_mul] at he
    calc
      _ = Real.exp ((k * (t : ℝ)) * (1-δ)) := by congr 1; ring
      _ ≤ _ := he.trans hsize
  have hlab : (6 * D : ℝ) ≤ S.card := by
    calc
      _ ≤ 6 * Real.exp (L * (t : ℝ)) := by gcongr
      _ ≤ Real.exp (((1-δ)*k-L) * (t : ℝ)) * Real.exp (L * (t : ℝ)) :=
        mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
      _ = Real.exp (((1-δ)*k) * (t : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hSexp
  exact ⟨p, hp, hpodd, hp8, hpup, S, hS, hfree, hcard, by exact_mod_cast hlab, hsize⟩

/-- Every strict entropy gap supplies actual prime/AP parameters and an
integer copy count for classical three-mode isolation. -/
theorem eventually_uniform_coarse_budget (H L ρ : ℝ)
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hgap : ρ < H-L) :
    ∃ a l : ℝ, a < H ∧ L < l ∧
      ∀ᶠ t : ℕ in atTop, ∀ D T : ℕ,
        (D : ℝ) ≤ Real.exp (l * (t : ℝ)) →
        Real.exp (a * (t : ℝ)) ≤ (T : ℝ) →
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 < p ∧
          ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧ ThreeAPFree (S : Set ℕ) ∧
            0 < S.card ∧ 6 * D ≤ S.card ∧
            ∃ r : ℕ, Real.exp (ρ * (t : ℝ)) ≤ (r : ℝ) ∧
              2 * p^2 * r ≤ T * S.card := by
  let b := (L + (H-ρ)) / 2
  let k := (L+b) / 2
  let l := (L+k) / 2
  let a := (H+(ρ+b)) / 2
  have hLb : L < b := by dsimp [b]; linarith
  have hbH : ρ+b < H := by dsimp [b]; linarith
  have hb : 0 < b := hL.trans_lt hLb
  have hLk : L < k := by dsimp [k]; linarith
  have hkb : k < b := by dsimp [k]; linarith
  have hk : 0 < k := hL.trans_lt hLk
  have hLl : L < l := by dsimp [l]; linarith
  have hlk : l < k := by dsimp [l]; linarith
  have hl : 0 ≤ l := hL.trans hLl.le
  have haH : a < H := by dsimp [a]; linarith
  have hba : ρ+b < a := by dsimp [a]; linarith
  let δ := min ((k-l)/(2*k)) ((a-(ρ+b))/(2*b))
  have hδ : 0 < δ := lt_min (div_pos (sub_pos.mpr hlk) (by positivity))
    (div_pos (sub_pos.mpr hba) (by positivity))
  have hδk : δ * k ≤ (k-l)/2 := by
    have h := (mul_le_mul_of_nonneg_right (min_le_left ((k-l)/(2*k)) ((a-(ρ+b))/(2*b))) hk.le)
    have he : (k-l)/(2*k)*k = (k-l)/2 := by field_simp
    rw [he] at h
    exact h
  have hδb : δ * b ≤ (a-(ρ+b))/2 := by
    have h := (mul_le_mul_of_nonneg_right (min_le_right ((k-l)/(2*k)) ((a-(ρ+b))/(2*b))) hb.le)
    have he : (a-(ρ+b))/(2*b)*b = (a-(ρ+b))/2 := by field_simp
    rw [he] at h
    exact h
  have hδ1 : δ < 1 := by nlinarith
  have hlabgap : l < (1-δ)*k := by nlinarith
  have hcopygap : ρ+(1+δ)*b < a := by nlinarith
  have hhash := eventually_prime_labels l k b δ hk hkb hδ hδ1 hlabgap
  have hbudget := MME.DWZB2RateBudget.eventually_copy_budget_of_exp_bounds
    a b ρ δ hρ hδ.le hcopygap
  refine ⟨a, l, haH, hLl, ?_⟩
  filter_upwards [hhash, hbudget] with t ht hbgt
  intro D T hD hT
  obtain ⟨p, hp, hpodd, hp8, hpb, S, hS, hfree, hcard, hlabels, hs⟩ := ht D hD
  have hcopies := hbgt p S.card T hp.pos hpb hs hT
  refine ⟨p, hp, hpodd, hp8, S, hS, hfree, hcard, hlabels,
    ⌈Real.exp (ρ * (t : ℝ))⌉₊, hcopies.1, ?_⟩
  let r := ⌈Real.exp (ρ * (t : ℝ))⌉₊
  have hc : 8 * p^2 * (r * (3*t+2)) ≤ 3*T*S.card := hcopies.2
  have hsmall : 3 * (2 * p^2 * r) ≤ 8 * p^2 * (r * (3*t+2)) := by
    nlinarith [Nat.zero_le (p^2*r*t), Nat.zero_le (p^2*r)]
  have hh := hsmall.trans hc
  have he : 3*T*S.card = 3*(T*S.card) := by ring
  rw [he] at hh
  exact Nat.le_of_mul_le_mul_left hh (by decide : 0 < 3)

end MME.DWZC1CoarseHashRate



open BigOperators Filter MME.RecursiveThinSplit MME.RecursiveXHash
open MME.DWZC1CoarseCounts MME.DWZC1CoarseIsolation
open scoped Classical Topology
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

namespace MME.DWZC1CoarseAsymptotic

theorem maxStarDegree_pos {R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split 4 (parent r) → ℕ) : 0 < maxStarDegree m :=
  (starDegree_pos m 0).trans_le ((le_max_left _ _).trans (le_max_left _ _))

theorem starDegree_le_max {R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split 4 (parent r) → ℕ) (i : Fin 3) : starDegree m i ≤ maxStarDegree m := by
  fin_cases i
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

/-- A genuine induced address family, with no hash-state, degree, or size
budget left as a hypothesis. The rate is the minimum AFTER summing regions. -/
theorem eventual_induced_families (R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, Split 4 (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) (hn : 0 < ∑ r, n r)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hgap : ρ < min (min (blockEntropy m 0) (blockEntropy m 1)) (blockEntropy m 2)) :
    ∀ᶠ t : ℕ in atTop,
      ∃ kept : Finset (Address 4 R parent (fun r ↦ n r * t)),
        kept ⊆ target (scaled m t) ∧
        (∀ i : Fin 3, Function.Injective (fun a : kept ↦ block i a.val)) ∧
        (∀ x y z : kept, SupportedMix x.val y.val z.val → x = y ∧ y = z) ∧
        Real.exp (ρ * (t : ℝ)) ≤ (kept.card : ℝ) := by
  classical
  let H := jointEntropy m
  let L := max (max (H-blockEntropy m 0) (H-blockEntropy m 1)) (H-blockEntropy m 2)
  have hDrate := maxStarDegree_log_rate m
  have hL : 0 ≤ L := by
    apply ge_of_tendsto hDrate
    apply Filter.Eventually.of_forall
    intro t
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Real.log_nonneg
    exact_mod_cast (Nat.succ_le_iff.mpr (maxStarDegree_pos (scaled m t)))
  have hid : H-L = min (min (blockEntropy m 0) (blockEntropy m 1)) (blockEntropy m 2) := by
    dsimp [L]
    simp only [max_def, min_def]
    split_ifs <;> linarith
  obtain ⟨a, l, ha, hl, hbudget⟩ :=
    MME.DWZC1CoarseHashRate.eventually_uniform_coarse_budget H L ρ hL hρ (by rwa [hid])
  have hTrate := (jointCount_log_rate m).eventually (lt_mem_nhds ha)
  have hDupper := hDrate.eventually (gt_mem_nhds hl)
  filter_upwards [hbudget, hTrate, hDupper, eventually_gt_atTop 0] with t ht hT hD ht0
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hTb : Real.exp (a * (t : ℝ)) ≤ (jointCount (scaled m t) : ℝ) := by
    apply (Real.le_log_iff_exp_le (by exact_mod_cast jointCount_pos (scaled m t))).mp
    exact ((lt_div_iff₀ htR).mp hT).le
  have hDb : (maxStarDegree (scaled m t) : ℝ) ≤ Real.exp (l * (t : ℝ)) := by
    apply (Real.log_le_iff_le_exp (by exact_mod_cast maxStarDegree_pos (scaled m t))).mp
    exact ((div_lt_iff₀ htR).mp hD).le
  obtain ⟨p, hp, hpodd, hp8, S, hS, hfree, hcard, hlabels, copies, hcopies, hsize⟩ :=
    ht (maxStarDegree (scaled m t)) (jointCount (scaled m t)) hDb hTb
  letI : Fact p.Prime := ⟨hp⟩
  let nt : Fin R → ℕ := fun r ↦ n r * t
  have hnt : 0 < ∑ r, nt r := by
    simpa only [nt, Finset.sum_mul] using Nat.mul_pos hn ht0
  let N := (∑ r, nt r) - 1
  have hN : N+1 = ∑ r, nt r := by dsimp [N]; omega
  let e : Fin (N+1) ≃ (r : Fin R) × Fin (nt r) :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_sigma]; exact hN)
  have hm' (r : Fin R) : ∑ a, scaled m t r a = nt r := by
    simp only [scaled, nt]
    rw [← Finset.sum_mul, hm]
  have hdegree (i : Fin 3) (w : Address 4 R parent nt) (hw : w ∈ target (scaled m t)) :
      ((ambient (scaled m t)).filter (fun v ↦ block i v = block i w)).card ≤
        maxStarDegree (scaled m t) := by
    rw [ambient_fiber_card 4 R parent hthin nt (scaled m t) i w
      (target_subset_ambient (scaled m t) hw)]
    exact starDegree_le_max (scaled m t) i
  obtain ⟨q, kept, hkept, hinj, hinduced, hmass⟩ :=
    finite_three_mode_isolation 4 R parent nt (scaled m t) hpodd (by omega)
      e S hS hfree (maxStarDegree (scaled m t)) hdegree hlabels
  refine ⟨kept, fun w hw ↦ (Finset.mem_filter.mp (hkept hw)).1, hinj, hinduced, ?_⟩
  have htarget : (target (n := nt) (scaled m t)).card = jointCount (scaled m t) :=
    target_card 4 R parent nt (scaled m t) hm'
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsizeR : 2*(p : ℝ)^2*(copies : ℝ) ≤ (jointCount (scaled m t) : ℝ)*S.card := by
    exact_mod_cast hsize
  apply hcopies.trans
  apply le_trans _ hmass
  rw [htarget]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(p : ℝ)^2)).mpr
  nlinarith

end MME.DWZC1CoarseAsymptotic


theorem solution (R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, Split 4 (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) (hn : 0 < ∑ r, n r) :
    let M := fun (r : Fin R) (i : Fin 3) (j : Fin 5) ↦
      ∑ a : {a : Split 4 (parent r) // a.val i = j}, m r a.val
    let HM := fun i : Fin 3 ↦ ∑ r,
      (((∑ j, M r i j : ℕ) : ℝ) * Real.log ((∑ j, M r i j : ℕ) : ℝ) -
        ∑ j, (M r i j : ℝ) * Real.log (M r i j : ℝ))
    ∀ ρ : ℝ, 0 ≤ ρ → ρ < min (min (HM 0) (HM 1)) (HM 2) →
      ∀ᶠ t : ℕ in atTop,
        ∃ kept : Finset (Address 4 R parent (fun r ↦ n r * t)),
          kept ⊆ target (fun r a ↦ m r a * t) ∧
          (∀ i : Fin 3, Function.Injective (fun a : kept ↦ block i a.val)) ∧
          (∀ x y z : kept,
            (∀ r s, ((x.val r s).val 0).val + ((y.val r s).val 1).val +
              ((z.val r s).val 2).val = 4) → x = y ∧ y = z) ∧
          Real.exp (ρ * (t : ℝ)) ≤ (kept.card : ℝ) := by
  dsimp only
  intro ρ hρ hgap
  exact MME.DWZC1CoarseAsymptotic.eventual_induced_families R parent hthin n m hm hn ρ hρ hgap
