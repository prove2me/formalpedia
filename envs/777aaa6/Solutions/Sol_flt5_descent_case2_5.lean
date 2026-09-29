-- Prove2me | solution 5 for flt5_descent_case2
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:13:32.122691+00:00
-- url     : https://prove2.me/submissions/760b541e-7668-41f9-be83-807ff647f758
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt5_descent_step
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

-- Sketch: flt5_descent_case2
-- Proof: infinite descent via strong induction on c.natAbs, using flt5_descent_step.
-- Child: flt5_descent_step

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) : False := by
  suffices key : ∀ n : ℕ, ∀ a b c : ℤ,
      a ^ 5 + b ^ 5 = c ^ 5 → Int.gcd a b = 1 → (5 : ℤ) ∣ c → c ≠ 0 → c.natAbs ≤ n → False by
    exact key c.natAbs a b c h_eq h_cop h5c hc (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro a b c _ _ _ hc hn
    exact hc (Int.natAbs_eq_zero.mp (Nat.le_zero.mp hn))
  | succ n ih =>
    intro a b c h_eq h_cop h5c hc hn
    obtain ⟨a', b', c', h_eq', h_cop', h5c', hc', hlt⟩ :=
      flt5_descent_step a b c h_eq h_cop h5c hc
    exact ih a' b' c' h_eq' h_cop' h5c' hc'
      (Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt hn))
