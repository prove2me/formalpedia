-- Prove2me | solution 1 for lean_workbook_plus_11423
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:20:48.816725+00:00
-- url     : https://prove2.me/submissions/ea2aef89-55de-463d-9988-9371a635d2b3

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

theorem riccati_rational_supersolution (C t : ℝ) (hC : 0 < C) (ht : 0 < t) :
    C * t / (t + C + 1) + (C * t / (t + C + 1)) ^ 2 / t ^ 2 <
      C * (t + 1) / (t + C + 2) := by
  have h1 : t + C + 1 ≠ 0 := by positivity
  have h2 : t + C + 2 ≠ 0 := by positivity
  have he : C * (t + 1) / (t + C + 2) -
      (C * t / (t + C + 1) + (C * t / (t + C + 1)) ^ 2 / t ^ 2) =
      C * (t + 1) / ((t + C + 1) ^ 2 * (t + C + 2)) := by
    field_simp
    ring
  have hp : 0 < C * (t + 1) / ((t + C + 1) ^ 2 * (t + C + 2)) := by positivity
  linarith

theorem riccati_supersolution_lt_constant (C t : ℝ) (hC : 0 < C) (ht : 0 < t) :
    C * t / (t + C + 1) < C := by
  apply (div_lt_iff₀ (by positivity : 0 < t + C + 1)).mpr
  nlinarith [mul_pos hC (show 0 < C + 1 by linarith)]

theorem variable_riccati_shifted_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (y : ℕ → ℝ) (h0 : y 0 = a)
    (hr : ∀ k, y (k + 1) = y k + (y k) ^ 2 / ((k : ℝ) + 1) ^ 2) (k : ℕ) :
    0 < y k ∧ y k ≤
      (2 * a / (1 - a)) * (k + 1) / ((k : ℝ) + 2 * a / (1 - a) + 2) := by
  let C : ℝ := 2 * a / (1 - a)
  have ha : 0 < 1 - a := by linarith
  have hC : 0 < C := div_pos (mul_pos (by norm_num) ha0) ha
  change 0 < y k ∧ y k ≤ C * (k + 1) / ((k : ℝ) + C + 2)
  induction k with
  | zero =>
    rw [h0]
    have he : C / (C + 2) = a := by
      apply (div_eq_iff (by positivity : C + 2 ≠ 0)).mpr
      dsimp [C]
      field_simp [ha.ne']
      ring
    simpa only [Nat.cast_zero, zero_add, mul_one, he] using And.intro ha0 (le_refl a)
  | succ k ih =>
    have ht : 0 < (k : ℝ) + 1 := by positivity
    have hB : 0 ≤ C * ((k : ℝ) + 1) / ((k : ℝ) + C + 2) := by positivity
    have hsq : (y k) ^ 2 ≤ (C * ((k : ℝ) + 1) / ((k : ℝ) + C + 2)) ^ 2 :=
      (sq_le_sq₀ ih.1.le hB).mpr ih.2
    have hi := add_le_add ih.2 (div_le_div_of_nonneg_right hsq (sq_nonneg ((k : ℝ) + 1)))
    have hs := riccati_rational_supersolution C ((k : ℝ) + 1) hC ht
    have hnorm : (k : ℝ) + 1 + C + 1 = (k : ℝ) + C + 2 := by ring
    rw [hnorm] at hs
    rw [hr k]
    constructor
    · have hp := ih.1
      positivity
    · convert (hi.trans hs.le) using 1 <;> push_cast <;> ring

theorem variable_riccati_shifted_uniform_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (y : ℕ → ℝ) (h0 : y 0 = a)
    (hr : ∀ k, y (k + 1) = y k + (y k) ^ 2 / ((k : ℝ) + 1) ^ 2) (k : ℕ) :
    0 < y k ∧ y k < 2 * a / (1 - a) := by
  have hb := variable_riccati_shifted_bound a ha0 ha1 y h0 hr k
  have hC : 0 < 2 * a / (1 - a) := div_pos (mul_pos (by norm_num) ha0) (by linarith)
  have hs := riccati_supersolution_lt_constant (2 * a / (1 - a)) ((k : ℝ) + 1) hC (by positivity)
  have he : (k : ℝ) + 1 + 2 * a / (1 - a) + 1 = (k : ℝ) + 2 * a / (1 - a) + 2 := by ring
  rw [he] at hs
  exact ⟨hb.1, hb.2.trans_lt hs⟩

theorem variable_riccati_shifted_strictMono (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (y : ℕ → ℝ) (h0 : y 0 = a)
    (hr : ∀ k, y (k + 1) = y k + (y k) ^ 2 / ((k : ℝ) + 1) ^ 2) : StrictMono y := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [hr k]
  have hp := (variable_riccati_shifted_uniform_bound a ha0 ha1 y h0 hr k).1
  have hd : 0 < (y k) ^ 2 / ((k : ℝ) + 1) ^ 2 := by positivity
  linarith

theorem variable_riccati_shifted_converges (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (y : ℕ → ℝ) (h0 : y 0 = a)
    (hr : ∀ k, y (k + 1) = y k + (y k) ^ 2 / ((k : ℝ) + 1) ^ 2) :
    ∃ L : ℝ, Tendsto y atTop (𝓝 L) ∧ a ≤ L ∧ L ≤ 2 * a / (1 - a) := by
  have hm := (variable_riccati_shifted_strictMono a ha0 ha1 y h0 hr).monotone
  have hb : BddAbove (Set.range y) := by
    refine ⟨2 * a / (1 - a), ?_⟩
    rintro z ⟨k, rfl⟩
    exact (variable_riccati_shifted_uniform_bound a ha0 ha1 y h0 hr k).2.le
  have ht := tendsto_atTop_ciSup hm hb
  refine ⟨⨆ k, y k, ht, ?_, ?_⟩
  · rw [← h0]
    exact le_ciSup hb 0
  · exact ciSup_le fun k => (variable_riccati_shifted_uniform_bound a ha0 ha1 y h0 hr k).2.le

theorem riccati_increment_tail_bound (C t v : ℝ) (hC : 0 ≤ C) (ht : 0 < t)
    (hv0 : 0 ≤ v) (hvC : v ≤ C) :
    v ^ 2 / (t + 1) ^ 2 ≤ C ^ 2 * (1 / t - 1 / (t + 1)) := by
  have hs : v ^ 2 ≤ C ^ 2 := (sq_le_sq₀ hv0 hC).mpr hvC
  have hd : C ^ 2 / (t + 1) ^ 2 ≤ C ^ 2 / (t * (t + 1)) :=
    div_le_div_of_nonneg_left (sq_nonneg C) (by positivity) (by nlinarith)
  have he : C ^ 2 / (t * (t + 1)) = C ^ 2 * (1 / t - 1 / (t + 1)) := by
    field_simp
    ring
  exact (div_le_div_of_nonneg_right hs (sq_nonneg (t + 1))).trans (hd.trans_eq he)

theorem variable_riccati_shifted_finite_tail (C : ℝ) (hC : 0 ≤ C)
    (y : ℕ → ℝ) (hb : ∀ k, 0 ≤ y k ∧ y k ≤ C)
    (hr : ∀ k, y (k + 1) = y k + (y k) ^ 2 / ((k : ℝ) + 1) ^ 2)
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    y (n + m) + C ^ 2 / (n + m) ≤ y n + C ^ 2 / n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ht : 0 < (n : ℝ) + m := by exact_mod_cast (show 0 < n + m by omega)
    have hs := riccati_increment_tail_bound C (n + m) (y (n + m)) hC ht
      (hb (n + m)).1 (hb (n + m)).2
    rw [Nat.add_succ, Nat.succ_eq_add_one, hr]
    push_cast at hs ih ⊢
    have he : C ^ 2 * (1 / (n + m) - 1 / (n + m + 1)) =
        C ^ 2 / (n + m) - C ^ 2 / (n + m + 1) := by ring
    rw [he] at hs
    rw [← add_assoc (n : ℝ) m 1]
    linarith

theorem variable_riccati_shifted_limit_tail (C L : ℝ) (hC : 0 ≤ C)
    (y : ℕ → ℝ) (hb : ∀ k, 0 ≤ y k ∧ y k ≤ C)
    (hr : ∀ k, y (k + 1) = y k + (y k) ^ 2 / ((k : ℝ) + 1) ^ 2)
    (hL : Tendsto y atTop (𝓝 L)) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ L - y n ∧ L - y n ≤ C ^ 2 / n := by
  have hm : Monotone y := monotone_nat_of_le_succ fun k => by
    rw [hr k]
    exact le_add_of_nonneg_right (by positivity)
  constructor
  · have hyL : y n ≤ L := ge_of_tendsto hL (eventually_atTop.2 ⟨n, fun k hk => hm hk⟩)
    linarith
  · have ht : Tendsto (fun m => y (n + m)) atTop (𝓝 L) := by
      simpa only [Nat.add_comm n] using (tendsto_add_atTop_iff_nat n).mpr hL
    have hle : L ≤ y n + C ^ 2 / n := le_of_tendsto ht (Eventually.of_forall fun m => by
      have h := variable_riccati_shifted_finite_tail C hC y hb hr n hn m
      have hp : 0 ≤ C ^ 2 / ((n : ℝ) + m) := by positivity
      linarith)
    linarith

theorem variable_riccati_source_bound (x : ℕ → ℝ) (h0 : 0 < x 1) (h1 : x 1 < 1)
    (hr : ∀ n, 1 ≤ n → x (n + 1) = x n + (x n) ^ 2 / (n : ℝ) ^ 2)
    (n : ℕ) (hn : 1 ≤ n) : 0 < x n ∧ x n < 2 * x 1 / (1 - x 1) := by
  have hs : ∀ k, x (k + 1 + 1) = x (k + 1) + (x (k + 1)) ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    intro k
    simpa only [Nat.cast_add, Nat.cast_one] using hr (k + 1) (by omega)
  have hb := variable_riccati_shifted_uniform_bound (x 1) h0 h1
    (fun k => x (k + 1)) rfl hs (n - 1)
  simpa only [Nat.sub_add_cancel hn] using hb

theorem variable_riccati_source_bounded (x : ℕ → ℝ) (h0 : 0 < x 1) (h1 : x 1 < 1)
    (hr : ∀ n, 1 ≤ n → x (n + 1) = x n + (x n) ^ 2 / (n : ℝ) ^ 2) :
    ∃ M, ∀ n, |x n| < M := by
  refine ⟨max |x 0| (2 * x 1 / (1 - x 1)) + 1, ?_⟩
  intro n
  cases n with
  | zero => linarith [le_max_left |x 0| (2 * x 1 / (1 - x 1))]
  | succ k =>
    have hb := variable_riccati_source_bound x h0 h1 hr (k + 1) (by omega)
    rw [abs_of_pos hb.1]
    linarith [le_max_right |x 0| (2 * x 1 / (1 - x 1))]

theorem variable_riccati_source_converges_with_rate (x : ℕ → ℝ)
    (h0 : 0 < x 1) (h1 : x 1 < 1)
    (hr : ∀ n, 1 ≤ n → x (n + 1) = x n + (x n) ^ 2 / (n : ℝ) ^ 2) :
    ∃ L : ℝ, Tendsto x atTop (𝓝 L) ∧ x 1 ≤ L ∧ L ≤ 2 * x 1 / (1 - x 1) ∧
      ∀ n : ℕ, 2 ≤ n → 0 ≤ L - x n ∧
        L - x n ≤ (2 * x 1 / (1 - x 1)) ^ 2 / (n - 1) := by
  let y := fun k => x (k + 1)
  have hs : ∀ k, y (k + 1) = y k + (y k) ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    intro k
    simpa only [y, Nat.cast_add, Nat.cast_one] using hr (k + 1) (by omega)
  obtain ⟨L, hL, hlow, hupp⟩ := variable_riccati_shifted_converges (x 1) h0 h1 y rfl hs
  refine ⟨L, (tendsto_add_atTop_iff_nat 1).mp hL, hlow, hupp, ?_⟩
  intro n hn
  have hb : ∀ k, 0 ≤ y k ∧ y k ≤ 2 * x 1 / (1 - x 1) := by
    intro k
    have h := variable_riccati_shifted_uniform_bound (x 1) h0 h1 y rfl hs k
    exact ⟨h.1.le, h.2.le⟩
  have hC : 0 ≤ 2 * x 1 / (1 - x 1) := le_of_lt (div_pos (by positivity) (by linarith))
  have ht := variable_riccati_shifted_limit_tail (2 * x 1 / (1 - x 1)) L hC y hb hs hL
    (n - 1) (by omega)
  simpa only [y, Nat.sub_add_cancel (show 1 ≤ n by omega), Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_one] using ht

theorem solution (x : ℕ → ℝ) (hx : ∀ n, 0 < x n ∧ x n < 1)
    (hn : ∀ n, x (n + 1) = x n + (x n) ^ 2 / (n : ℝ) ^ 2) :
    ∃ M, ∀ n, abs (x n) < M := by
  exact variable_riccati_source_bounded x (hx 1).1 (hx 1).2 (fun n _ => hn n)

#print axioms riccati_rational_supersolution
#print axioms riccati_supersolution_lt_constant
#print axioms variable_riccati_shifted_bound
#print axioms variable_riccati_shifted_uniform_bound
#print axioms variable_riccati_shifted_strictMono
#print axioms variable_riccati_shifted_converges
#print axioms riccati_increment_tail_bound
#print axioms variable_riccati_shifted_finite_tail
#print axioms variable_riccati_shifted_limit_tail
#print axioms variable_riccati_source_bound
#print axioms variable_riccati_source_bounded
#print axioms variable_riccati_source_converges_with_rate
#print axioms solution
