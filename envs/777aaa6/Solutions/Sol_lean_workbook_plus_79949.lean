-- Prove2me | solution 1 for lean_workbook_plus_79949
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:08:31.591486+00:00
-- url     : https://prove2.me/submissions/35a8ad2a-39f4-43f9-82bb-a063be796bc3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

lemma recover_natural_subtrahend (base tail total removed : ℕ)
    (hbase : 0 < base) (htotal : total = base + tail)
    (hsub : total - removed = base) : removed = tail := by
  omega

theorem solution (u v t n : ℕ) (f g : ℕ → ℕ)
    (h₀ : n = 2 ^ u - 2 ^ v + t) (h₁ : u > v) (h₂ : v >= 0)
    (h₃ : t < 2 ^ (v - 1)) (h₄ : f n = 2 ^ v - t - 1)
    (h₅ : g n = f (f n)) (h₆ : n - g n = 2 ^ u - 2 ^ v)
    (h₇ : f (n - g n) = 2 ^ v - 1)
    (h₈ : g (n - g n) = f (2 ^ v - 1)) (h₉ : f (2 ^ v - 1) = 0) :
    g n = t := by
  have hp : (2 : ℕ) ^ v < 2 ^ u := Nat.pow_lt_pow_right (by decide) h₁
  exact recover_natural_subtrahend (2 ^ u - 2 ^ v) t n (g n)
    (Nat.sub_pos_of_lt hp) h₀ h₆

#print axioms solution
