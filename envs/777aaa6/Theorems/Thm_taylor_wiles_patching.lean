-- Prove2me | Theorems.Thm_taylor_wiles_patching
-- name    : taylor_wiles_patching
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-12T05:21:10.226086+00:00
-- url     : https://prove2.me/theorems/4bb33c19-530c-4fc8-83cd-1fcfbd30185d
-- statement:
--   **Taylor-Wiles patching method (1995).** By choosing an infinite sequence of auxiliary 'Taylor-Wiles primes' Q_n and patching the associated Selmer groups and Hecke algebras over the Iwasawa algebra Λ = ℤ_p[[X₁,...,X_g]], one constructs a patched module M_∞ that is free of rank 1 over R_∞ ≅ Λ. The depth argument (Auslander-Buchsbaum + Cohen-Macaulay) then forces R_∞ → T_∞ to be an isomorphism, establishing R = T. This is the most technical step in Wiles's proof and requires the full machinery of commutative algebra over complete local rings.
-- source:
--   https://doi.org/10.2307/2118558

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem taylor_wiles_patching (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) : False := by sorry
