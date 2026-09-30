-- Prove2me | solution 1 for lean_workbook_plus_24817
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:56:42.397784+00:00
-- url     : https://prove2.me/submissions/ec4603b4-920d-4dfe-ba87-70352df132cd

import Mathlib.Analysis.Complex.Basic

namespace CoprimePeriodsConstant

theorem add_period {A : Type*} (f : ℕ → A) {p q : ℕ}
    (hp : ∀ n, f (n + p) = f n) (hq : ∀ n, f (n + q) = f n) :
    ∀ n, f (n + (p + q)) = f n := by
  intro n
  calc
    f (n + (p + q)) = f ((n + p) + q) := by rw [Nat.add_assoc]
    _ = f (n + p) := hq (n + p)
    _ = f n := hp n

theorem sub_period {A : Type*} (f : ℕ → A) {p q : ℕ}
    (hp : ∀ n, f (n + p) = f n) (hq : ∀ n, f (n + q) = f n)
    (hpq : p ≤ q) : ∀ n, f (n + (q - p)) = f n := by
  intro n
  calc
    f (n + (q - p)) = f ((n + (q - p)) + p) := (hp (n + (q - p))).symm
    _ = f (n + q) := by rw [Nat.add_assoc, Nat.sub_add_cancel hpq]
    _ = f n := hq n

theorem constant_of_nine_sixteen {A : Type*} (f : ℕ → A)
    (h9 : ∀ n, f (n + 9) = f n) (h16 : ∀ n, f (n + 16) = f n) :
    ∀ n, f n = f 0 := by
  have h7 : ∀ n, f (n + 7) = f n := sub_period f h9 h16 (by decide)
  have h2 : ∀ n, f (n + 2) = f n := sub_period f h7 h9 (by decide)
  have h4 : ∀ n, f (n + 4) = f n := add_period f h2 h2
  have h6 : ∀ n, f (n + 6) = f n := add_period f h2 h4
  have h1 : ∀ n, f (n + 1) = f n := sub_period f h6 h7 (by decide)
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact (h1 n).trans ih

theorem constant_iff_nine_sixteen {A : Type*} (f : ℕ → A) :
    (∀ n, f n = f 0) ↔
      (∀ n, f (n + 9) = f n) ∧ (∀ n, f (n + 16) = f n) := by
  constructor
  · intro h
    exact ⟨fun n => (h (n + 9)).trans (h n).symm,
      fun n => (h (n + 16)).trans (h n).symm⟩
  · rintro ⟨h9, h16⟩
    exact constant_of_nine_sixteen f h9 h16

end CoprimePeriodsConstant

theorem solution (f : ℕ → ℝ) (h9 : ∀ n, f (n + 9) = f n)
    (h16 : ∀ n, f (n + 16) = f n) : ∀ n, f n = f 0 := by
  exact CoprimePeriodsConstant.constant_of_nine_sixteen f h9 h16
