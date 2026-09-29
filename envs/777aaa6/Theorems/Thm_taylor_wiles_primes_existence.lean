-- Prove2me | Theorems.Thm_taylor_wiles_primes_existence
-- name    : taylor_wiles_primes_existence
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-12T05:25:16.409564+00:00
-- url     : https://prove2.me/theorems/5e0575d4-8832-4ccc-a1df-ad798aaa84e2
-- statement:
--   **Existence of Taylor-Wiles primes.** For each n ≥ 1, there exist primes q_{n,1}, ..., q_{n,g} (the Taylor-Wiles primes at level n) satisfying: (1) q_{n,i} ≡ 1 (mod p^n), (2) the residual Galois representation ρ̄(Frob_{q_{n,i}}) has distinct eigenvalues (i.e., ρ̄ is unramified at q_{n,i} with Frobenius having two distinct eigenvalues mod p), and (3) the Selmer condition at q_{n,i} is suitably controlled. The existence of such primes follows from the Chebotarev density theorem applied to the splitting field of ρ̄[p^n]. These primes are used to construct the patching system in the Taylor-Wiles method.
-- source:
--   https://doi.org/10.2307/2118558

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem taylor_wiles_primes_existence (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) : False := by sorry
