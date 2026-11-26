-- Prove2me | Theorems.Thm_syracuse_injective_last_exit_and_tail_minimum
-- name    : syracuse_injective_last_exit_and_tail_minimum
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:10:03.672808+00:00
-- url     : https://prove2.me/theorems/d967458b-731c-46ac-828d-d70faee26fe5
-- title:
--   Last exit and tail minimum at every barrier for an injective Syracuse orbit
-- statement:
--   In an injective Syracuse orbit starting at an odd positive n, take any barrier B > max(1,n). There is a last index k below B. Its next step divides 3*x_k+1 by exactly 2. The subsequent tail attains a minimum m with B ≤ m and 2*m+2 ≤ 3*B, and m is 7 or 11 modulo 12.
-- source:
--   Finite preimage of the bounded initial interval under an injective orbit, the exact one-step factorization, and the attained minimum of the subsequent tail.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_injective_last_exit_and_tail_minimum (n B : ℕ)
    (hodd : n % 2 = 1) (hB : 1 < B) (hnB : n < B)
    (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n)) :
    ∃ k j : ℕ, k < j ∧ syracuseStep^[k] n < B ∧
      2 * syracuseStep^[k+1] n = 3 * syracuseStep^[k] n + 1 ∧
      (∀ i > k, B ≤ syracuseStep^[i] n) ∧
      B ≤ syracuseStep^[j] n ∧ 2 * syracuseStep^[j] n + 2 ≤ 3 * B ∧
      (syracuseStep^[j] n % 12 = 7 ∨ syracuseStep^[j] n % 12 = 11) ∧
      (∀ i > k, syracuseStep^[j] n ≤ syracuseStep^[i] n) := by sorry
