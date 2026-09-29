-- Prove2me | solution 1 for AsymmetricExponent.powMod_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:26:14.772003+00:00
-- url     : https://prove2.me/submissions/10dc4f82-3246-4318-938f-2e9f9fe67519

-- Sol generated from Cryptography/AsymmetricExponent/PolyTime.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core
import Definitions.Def_Cryptography_AsymmetricExponent_PolyTime

/-!
# `Q(a) = a^(N-1) mod N` is cheap: a verified logarithmic-cost algorithm

The FETQ quantity is interesting only because it costs nothing to compute.
This file makes that precise inside Lean: a binary (square-and-multiply)
modular exponentiation routine is defined, proved **correct**, and its
recursion depth is proved to be at most the binary length `Nat.size` of the
exponent.  Computing `Q(a)` therefore costs `O(log N)` modular multiplications
— no factorisation, no aggregation over many `a`.

Main results.

* `AsymmetricExponent.powMod_eq` — `powMod m a n = a^n % m` (strong induction on
  the exponent).
* `AsymmetricExponent.powModSteps_le_size` — the number of recursive halvings
  is at most `Nat.size n`.
* `AsymmetricExponent.fetq_eq_powMod` and
  `AsymmetricExponent.fetq_cost_logarithmic` — the FETQ quantity is computed by
  this routine at logarithmic cost.
-/

open AsymmetricExponent








open AsymmetricExponent in
theorem solution(m a : ℕ) : ∀ n : ℕ, powMod m a n = a ^ n % m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [powMod]
    | (k + 1) =>
      have hlt : (k + 1) / 2 < k + 1 := by omega
      have ihk := ih ((k + 1) / 2) hlt
      rw [powMod]
      simp only [ihk]
      rcases Nat.even_or_odd (k + 1) with hev | hodd
      · have hmod : (k + 1) % 2 = 0 := Nat.even_iff.mp hev
        have hsplit : a ^ (k + 1) = a ^ ((k + 1) / 2) * a ^ ((k + 1) / 2) := by
          rw [← pow_add]; congr 1; omega
        rw [if_pos hmod, hsplit, Nat.mul_mod]
        simp
      · have hmod : (k + 1) % 2 = 1 := Nat.odd_iff.mp hodd
        have hsplit : a ^ (k + 1) = a ^ ((k + 1) / 2) * a ^ ((k + 1) / 2) * a := by
          rw [← pow_add, ← pow_succ]; congr 1; omega
        rw [if_neg (by omega), hsplit, Nat.mul_mod (a ^ ((k + 1) / 2) * a ^ ((k + 1) / 2)) a,
          Nat.mul_mod (a ^ ((k + 1) / 2))]
