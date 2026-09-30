-- Prove2me | solution 1 for lean_workbook_plus_15360
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:26:58.435267+00:00
-- url     : https://prove2.me/submissions/4e4dcd45-acec-49cc-b42f-c7844743db5f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

theorem fibonacci_rational_positive (u : ℕ → ℝ) (h0 : u 0 = 1 / 2) (h1 : u 1 = 3)
    (hr : ∀ n, u (n + 2) = (u (n + 1) * u n + 1) / (u (n + 1) + u n))
    (n : ℕ) : 0 < u n := by
  induction n using Nat.twoStepInduction with
  | zero => rw [h0]; norm_num
  | one => rw [h1]; norm_num
  | more n ih ih' => rw [hr n]; positivity

theorem fibonacci_rational_transform_identity (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (((s * t + 1) / (s + t)) - 1) / (((s * t + 1) / (s + t)) + 1) =
      ((s - 1) / (s + 1)) * ((t - 1) / (t + 1)) := by
  have hst : s + t ≠ 0 := by positivity
  have hs1 : s + 1 ≠ 0 := by positivity
  have ht1 : t + 1 ≠ 0 := by positivity
  have hn : s * t + 1 + (s + t) ≠ 0 := by positivity
  field_simp
  ring

theorem fibonacci_rational_transform_recurrence (u : ℕ → ℝ)
    (h0 : u 0 = 1 / 2) (h1 : u 1 = 3)
    (hr : ∀ n, u (n + 2) = (u (n + 1) * u n + 1) / (u (n + 1) + u n))
    (n : ℕ) : (u (n + 2) - 1) / (u (n + 2) + 1) =
      ((u (n + 1) - 1) / (u (n + 1) + 1)) * ((u n - 1) / (u n + 1)) := by
  rw [hr n]
  exact fibonacci_rational_transform_identity _ _
    (fibonacci_rational_positive u h0 h1 hr (n + 1)) (fibonacci_rational_positive u h0 h1 hr n)

theorem multiplicative_fibonacci_formula (v : ℕ → ℝ) (p q : ℝ)
    (h0 : v 0 = p) (h1 : v 1 = q) (hr : ∀ n, v (n + 2) = v (n + 1) * v n)
    (n : ℕ) : v (n + 1) = p ^ Nat.fib n * q ^ Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using h1
  | one => rw [hr 0, h0, h1]; norm_num; ring
  | more n ih ih' =>
    have he : n + 2 + 1 = n + 1 + 2 := by omega
    rw [he, hr (n + 1), show n + 1 + 1 = n + 2 by omega, ih', ih]
    have hf2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have hf3 : Nat.fib (n + 2 + 1) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      simpa only [Nat.add_assoc] using (Nat.fib_add_two (n := n + 1))
    rw [hf3, hf2]
    simp only [pow_add]
    ring

theorem multiplicative_fibonacci_half_bound (v : ℕ → ℝ)
    (h0 : v 0 = -(1 / 3)) (h1 : v 1 = 1 / 2)
    (hr : ∀ n, v (n + 2) = v (n + 1) * v n) (n : ℕ) : |v n| ≤ 1 / 2 := by
  induction n using Nat.twoStepInduction with
  | zero => rw [h0]; norm_num
  | one => rw [h1]; norm_num
  | more n ih ih' =>
    rw [hr n, abs_mul]
    have hm := mul_le_mul ih' ih (abs_nonneg (v n)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at hm ⊢
    linarith

theorem multiplicative_fibonacci_geometric_bound (v : ℕ → ℝ)
    (h0 : v 0 = -(1 / 3)) (h1 : v 1 = 1 / 2)
    (hr : ∀ n, v (n + 2) = v (n + 1) * v n) (n : ℕ) :
    |v (n + 1)| ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => rw [h1]; norm_num
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, hr n, abs_mul]
    have hb := multiplicative_fibonacci_half_bound v h0 h1 hr n
    have hm := mul_le_mul ih hb (abs_nonneg (v n)) (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (n + 1))
    simpa only [pow_succ] using hm

theorem multiplicative_fibonacci_tendsto_zero (v : ℕ → ℝ)
    (h0 : v 0 = -(1 / 3)) (h1 : v 1 = 1 / 2)
    (hr : ∀ n, v (n + 2) = v (n + 1) * v n) : Tendsto v atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have ha := squeeze_zero (fun n => abs_nonneg (v (n + 1)))
    (multiplicative_fibonacci_geometric_bound v h0 h1 hr) hp
  have ht : Tendsto (fun n => v (n + 1)) atTop (𝓝 0) := by
    apply (tendsto_iff_norm_sub_tendsto_zero (f := fun n => v (n + 1)) (b := (0 : ℝ))).mpr
    simpa only [sub_zero, Real.norm_eq_abs] using ha
  exact (tendsto_add_atTop_iff_nat 1).mp ht

theorem multiplicative_fibonacci_signs (v : ℕ → ℝ)
    (h0 : v 0 = -(1 / 3)) (h1 : v 1 = 1 / 2)
    (hr : ∀ n, v (n + 2) = v (n + 1) * v n) (k : ℕ) :
    v (3 * k) < 0 ∧ 0 < v (3 * k + 1) ∧ v (3 * k + 2) < 0 := by
  induction k with
  | zero =>
    have h2 := hr 0
    norm_num [h0, h1] at h2 ⊢
    linarith
  | succ k ih =>
    have h3 : v (3 * k + 3) < 0 := by
      rw [show 3 * k + 3 = (3 * k + 1) + 2 by omega, hr]
      exact mul_neg_of_neg_of_pos ih.2.2 ih.2.1
    have h4 : 0 < v (3 * k + 4) := by
      rw [show 3 * k + 4 = (3 * k + 2) + 2 by omega, hr]
      exact mul_pos_of_neg_of_neg h3 ih.2.2
    have h5 : v (3 * k + 5) < 0 := by
      rw [show 3 * k + 5 = (3 * k + 3) + 2 by omega, hr]
      exact mul_neg_of_pos_of_neg h4 h3
    convert And.intro h3 (And.intro h4 h5) using 1

theorem positive_fraction_recover (t : ℝ) (ht : 0 < t) :
    t = (1 + (t - 1) / (t + 1)) / (1 - (t - 1) / (t + 1)) := by
  have ht1 : t + 1 ≠ 0 := by positivity
  have hv : (t - 1) / (t + 1) < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < t + 1)).mpr
    linarith
  have hd : 1 - (t - 1) / (t + 1) ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  field_simp
  ring

theorem fibonacci_rational_full_formula (u : ℕ → ℝ) (h0 : u 0 = 1 / 2) (h1 : u 1 = 3)
    (hr : ∀ n, u (n + 2) = (u (n + 1) * u n + 1) / (u (n + 1) + u n)) (n : ℕ) :
    u (n + 1) =
      (1 + (-(1 / 3 : ℝ)) ^ Nat.fib n * (1 / 2 : ℝ) ^ Nat.fib (n + 1)) /
      (1 - (-(1 / 3 : ℝ)) ^ Nat.fib n * (1 / 2 : ℝ) ^ Nat.fib (n + 1)) := by
  let v := fun k => (u k - 1) / (u k + 1)
  have hv0 : v 0 = -(1 / 3) := by dsimp [v]; rw [h0]; ring
  have hv1 : v 1 = 1 / 2 := by dsimp [v]; rw [h1]; ring
  have hvr := fibonacci_rational_transform_recurrence u h0 h1 hr
  have hf := multiplicative_fibonacci_formula v _ _ hv0 hv1 hvr n
  rw [← hf]
  exact positive_fraction_recover _ (fibonacci_rational_positive u h0 h1 hr (n + 1))

theorem fibonacci_rational_converges (u : ℕ → ℝ) (h0 : u 0 = 1 / 2) (h1 : u 1 = 3)
    (hr : ∀ n, u (n + 2) = (u (n + 1) * u n + 1) / (u (n + 1) + u n)) :
    Tendsto u atTop (𝓝 1) := by
  let v := fun k => (u k - 1) / (u k + 1)
  have hv0 : v 0 = -(1 / 3) := by dsimp [v]; rw [h0]; ring
  have hv1 : v 1 = 1 / 2 := by dsimp [v]; rw [h1]; ring
  have ht := multiplicative_fibonacci_tendsto_zero v hv0 hv1
    (fibonacci_rational_transform_recurrence u h0 h1 hr)
  have he : u = fun n => (1 + v n) / (1 - v n) := by
    funext n
    exact positive_fraction_recover _ (fibonacci_rational_positive u h0 h1 hr n)
  rw [he]
  simpa only [add_zero, sub_zero, div_one] using
    ((tendsto_const_nhds (x := (1 : ℝ))).add ht).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub ht) (by norm_num : (1 : ℝ) - 0 ≠ 0)

theorem fibonacci_rational_corrected_signs (u : ℕ → ℝ) (h0 : u 0 = 1 / 2) (h1 : u 1 = 3)
    (hr : ∀ n, u (n + 2) = (u (n + 1) * u n + 1) / (u (n + 1) + u n)) (k : ℕ) :
    u (3 * k) < 1 ∧ 1 < u (3 * k + 1) ∧ u (3 * k + 2) < 1 := by
  let v := fun j => (u j - 1) / (u j + 1)
  have hv0 : v 0 = -(1 / 3) := by dsimp [v]; rw [h0]; ring
  have hv1 : v 1 = 1 / 2 := by dsimp [v]; rw [h1]; ring
  have hs := multiplicative_fibonacci_signs v hv0 hv1
    (fibonacci_rational_transform_recurrence u h0 h1 hr) k
  have hneg : ∀ n, v n < 0 → u n < 1 := by
    intro n hn
    have hp : 0 < u n + 1 := by linarith [fibonacci_rational_positive u h0 h1 hr n]
    have he := (div_lt_iff₀ hp).mp hn
    linarith
  have hpos : ∀ n, 0 < v n → 1 < u n := by
    intro n hn
    have hp : 0 < u n + 1 := by linarith [fibonacci_rational_positive u h0 h1 hr n]
    have he := (div_pos_iff_of_pos_right hp).mp hn
    linarith
  exact ⟨hneg _ hs.1, hpos _ hs.2.1, hneg _ hs.2.2⟩

theorem fibonacci_rational_greater_one_iff (u : ℕ → ℝ)
    (h0 : u 0 = 1 / 2) (h1 : u 1 = 3)
    (hr : ∀ n, u (n + 2) = (u (n + 1) * u n + 1) / (u (n + 1) + u n))
    (n : ℕ) : 1 < u n ↔ n % 3 = 1 := by
  have hs := fibonacci_rational_corrected_signs u h0 h1 hr (n / 3)
  have hd := Nat.mod_add_div n 3
  have hm := Nat.mod_lt n (by norm_num : 0 < 3)
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
  · have hn : n = 3 * (n / 3) := by omega
    rw [hn] at h ⊢
    constructor
    · intro hp; linarith [hs.1]
    · intro he; omega
  · have hn : n = 3 * (n / 3) + 1 := by omega
    exact ⟨fun _ => h, fun _ => by simpa only [← hn] using hs.2.1⟩
  · have hn : n = 3 * (n / 3) + 2 := by omega
    constructor
    · intro hp
      rw [hn] at hp
      linarith [hs.2.2]
    · intro he; omega

noncomputable def fibonacciRationalOrbit (n : ℕ) : ℝ :=
  (Nat.rec (motive := fun _ => ℝ × ℝ) ((1 / 2 : ℝ), (3 : ℝ))
    (fun _ p => (p.2, (p.2 * p.1 + 1) / (p.2 + p.1))) n).1

theorem fibonacci_rational_orbit_zero : fibonacciRationalOrbit 0 = 1 / 2 := rfl

theorem fibonacci_rational_orbit_one : fibonacciRationalOrbit 1 = 3 := rfl

theorem fibonacci_rational_orbit_recurrence (n : ℕ) :
    fibonacciRationalOrbit (n + 2) =
      (fibonacciRationalOrbit (n + 1) * fibonacciRationalOrbit n + 1) /
      (fibonacciRationalOrbit (n + 1) + fibonacciRationalOrbit n) := rfl

theorem fibonacci_rational_orbit_result :
    Tendsto fibonacciRationalOrbit atTop (𝓝 1) ∧
    (∀ n, 0 < fibonacciRationalOrbit n) ∧
    (∀ n, 1 < fibonacciRationalOrbit n ↔ n % 3 = 1) := by
  exact ⟨fibonacci_rational_converges _ rfl rfl fibonacci_rational_orbit_recurrence,
    fibonacci_rational_positive _ rfl rfl fibonacci_rational_orbit_recurrence,
    fibonacci_rational_greater_one_iff _ rfl rfl fibonacci_rational_orbit_recurrence⟩

theorem solution : ¬ (∀ (u : ℕ → ℝ), u 0 = 1 / 2 → u 1 = 3 →
    (∀ n, u (n + 2) = (u (n + 1) * u n + 1) / (u (n + 1) + u n)) →
    ∀ n, u n > 1) := by
  intro h
  have hbad := h fibonacciRationalOrbit rfl rfl fibonacci_rational_orbit_recurrence 2
  change (1 : ℝ) < (3 * (1 / 2) + 1) / (3 + (1 / 2)) at hbad
  norm_num at hbad

#print axioms fibonacci_rational_positive
#print axioms fibonacci_rational_transform_identity
#print axioms fibonacci_rational_transform_recurrence
#print axioms multiplicative_fibonacci_formula
#print axioms multiplicative_fibonacci_half_bound
#print axioms multiplicative_fibonacci_geometric_bound
#print axioms multiplicative_fibonacci_tendsto_zero
#print axioms multiplicative_fibonacci_signs
#print axioms positive_fraction_recover
#print axioms fibonacci_rational_full_formula
#print axioms fibonacci_rational_converges
#print axioms fibonacci_rational_corrected_signs
#print axioms fibonacci_rational_greater_one_iff
#print axioms fibonacciRationalOrbit
#print axioms fibonacci_rational_orbit_zero
#print axioms fibonacci_rational_orbit_one
#print axioms fibonacci_rational_orbit_recurrence
#print axioms fibonacci_rational_orbit_result
#print axioms solution
