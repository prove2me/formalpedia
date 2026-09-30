-- Prove2me | solution 1 for lean_workbook_plus_69076
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:55:10.78944+00:00
-- url     : https://prove2.me/submissions/4c7e9401-e362-4ec2-8a67-d2dfe0cf743a

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private theorem choose_two_from_double (t v : ℕ)
    (h : t * (t - 1) = 2 * v) : t.choose 2 = v := by
  rw [Nat.choose_two_right, h]
  omega

private theorem positive_binomial_equation_ordered (a b : ℕ) (hba : b < a) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ (x + y).choose 2 = a * x + b * y := by
  let d := a - b
  let q := b / d
  let r := b % d
  let k := q + 1
  let u := 2 * d - 2 * r - 1
  let v := 2 * r + 1
  have hd : 0 < d := Nat.sub_pos_of_lt hba
  have hr : r < d := Nat.mod_lt b hd
  have hdiv : r + d * q = b := Nat.mod_add_div b d
  have hab : a = b + d := by dsimp [d]; omega
  have hu : 0 < u := by dsimp [u]; omega
  have hv : 0 < v := by dsimp [v]; omega
  have hk : 0 < k := Nat.zero_lt_succ q
  have huv : u + v = 2 * d := by dsimp [u, v]; omega
  have htotal : k * (2 * d) = 2 * b + u + 1 := by
    dsimp [k]
    have : u + 2 * r + 1 = 2 * d := by dsimp [u]; omega
    nlinarith
  refine ⟨k * u, k * v, Nat.mul_pos hk hu, Nat.mul_pos hk hv, ?_⟩
  apply choose_two_from_double
  have hsum : k * u + k * v = k * (2 * d) := by rw [← Nat.mul_add, huv]
  have hsub : k * (2 * d) - 1 = 2 * b + u := by omega
  rw [hsum, hsub, hab]
  calc
    _ = 2 * k * (b * (u + v) + d * u) := by rw [huv]; ring
    _ = _ := by ring

theorem positive_binomial_equation (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ (x + y).choose 2 = a * x + b * y := by
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨y, x, hy, hx, heq⟩ := positive_binomial_equation_ordered b a hab
    exact ⟨x, y, hx, hy, by simpa [Nat.add_comm] using heq⟩
  · subst b
    refine ⟨a, a + 1, ha, by omega, ?_⟩
    apply choose_two_from_double
    have hsub : a + (a + 1) - 1 = 2 * a := by omega
    rw [hsub]
    ring
  · exact positive_binomial_equation_ordered a b hab

theorem solution (a b : ℕ) (hab : 0 < a ∧ 0 < b) :
    ∃ x y : ℕ, Nat.choose (x + y) 2 = a * x + b * y := by
  obtain ⟨x, y, _, _, heq⟩ := positive_binomial_equation a b hab.1 hab.2
  exact ⟨x, y, heq⟩
