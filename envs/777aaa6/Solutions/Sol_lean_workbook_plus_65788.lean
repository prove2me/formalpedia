-- Prove2me | solution 1 for lean_workbook_plus_65788
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:31:00.204928+00:00
-- url     : https://prove2.me/submissions/64744f56-ccea-4976-bb5e-5a4d143377e1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

def pellPair : ℕ → ℕ × ℕ
  | 0 => (17, 6)
  | n + 1 => (17 * (pellPair n).1 + 48 * (pellPair n).2,
      6 * (pellPair n).1 + 17 * (pellPair n).2)

lemma pellPair_separated (n : ℕ) : (pellPair n).2 < (pellPair n).1 := by
  induction n with
  | zero => norm_num [pellPair]
  | succ n ih =>
    change 6 * (pellPair n).1 + 17 * (pellPair n).2 <
      17 * (pellPair n).1 + 48 * (pellPair n).2
    omega

lemma pellPair_mod_four (n : ℕ) : (pellPair n).1 ≡ 1 [ZMOD 4] := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h17 : (17 : ℤ) ≡ 1 [ZMOD 4] := by decide
    have h48 : (48 : ℤ) ≡ 0 [ZMOD 4] := by decide
    change ((17 * (pellPair n).1 + 48 * (pellPair n).2 : ℕ) : ℤ) ≡ 1 [ZMOD 4]
    push_cast
    simpa using (h17.mul ih).add (h48.mul (Int.ModEq.refl ((pellPair n).2 : ℤ)))

theorem solution
    (h : ∀ x y : ℕ → ℕ, x 0 = 17 → y 0 = 6 →
      (∀ n, x (n + 1) = 17 * x n + 48 * y n) →
      (∀ n, y (n + 1) = 6 * x n + 17 * y n) →
      (∀ n, x n ≡ 1 [ZMOD 4]) → ∃ n, 0 < n ∧ x n = y n) : False := by
  obtain ⟨n, _, heq⟩ := h (fun n => (pellPair n).1) (fun n => (pellPair n).2)
    rfl rfl (fun _ => rfl) (fun _ => rfl) pellPair_mod_four
  have hlt := pellPair_separated n
  omega

#print axioms solution
