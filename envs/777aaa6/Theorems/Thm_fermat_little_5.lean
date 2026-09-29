-- Prove2me | Theorems.Thm_fermat_little_5
-- name    : fermat_little_5
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:18:28.435658+00:00
-- url     : https://prove2.me/theorems/818c4435-4147-4661-8803-65f379fe94dc
-- statement:
--   **Fermat's Little Theorem for p = 5.** For any integer a, 5 divides a^5 − a. Equivalently, a^5 ≡ a (mod 5) for all integers a. This is the special case p=5 of Fermat's Little Theorem: for any prime p and any integer a, p | a^p − a. The result is used in Dirichlet's elementary proof of FLT for n=5, where one needs to analyze divisibility by 5 in the factorization (a+b)·Φ₅(a,b) = c^5.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem fermat_little_5 (a : ℤ) : (5 : ℤ) ∣ a ^ 5 - a := by sorry
