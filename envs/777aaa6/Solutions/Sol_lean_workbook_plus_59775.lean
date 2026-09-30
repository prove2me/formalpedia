-- Prove2me | solution 1 for lean_workbook_plus_59775
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:36:44.216333+00:00
-- url     : https://prove2.me/submissions/32f386c9-9be8-472c-bce0-290d029951ca

import Mathlib.Data.Nat.Basic

theorem solution (f : ℕ → ℕ)
    (hf : ∀ n : ℕ, n > 1 → 2 * f n > f (n - 1) + f (n + 1)) : False := by
  have slope : ∀ n : ℕ, f (n + 2) + f 1 + n ≤ f (n + 1) + f 2 := by
    intro n
    induction n with
    | zero => simp [Nat.add_comm]
    | succ n ih =>
      have hc := hf (n + 2) (by omega)
      have hsub : n + 2 - 1 = n + 1 := by omega
      rw [hsub] at hc
      change 2 * f (n + 2) > f (n + 1) + f (n + 3) at hc
      change f (n + 3) + f 1 + (n + 1) ≤ f (n + 2) + f 2
      omega
  have descent : ∀ k : ℕ, f (f 2 + k + 2) + k ≤ f (f 2 + 2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := slope (f 2 + k + 1)
      change f (f 2 + k + 3) + f 1 + (f 2 + k + 1) ≤
        f (f 2 + k + 2) + f 2 at hs
      change f (f 2 + k + 3) + (k + 1) ≤ f (f 2 + 2)
      omega
  have h := descent (f (f 2 + 2) + 1)
  omega

#print axioms solution
