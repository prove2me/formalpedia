-- Prove2me | solution 1 for AsymmetricExponent.powModSteps_le_size
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:26:14.139785+00:00
-- url     : https://prove2.me/submissions/14450f06-8443-40c4-ab8f-80e2e50066b8

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
theorem solution: ∀ n : ℕ, powModSteps n ≤ Nat.size n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [powModSteps]
    | (k + 1) =>
      have hlt : (k + 1) / 2 < k + 1 := by omega
      have ihk := ih ((k + 1) / 2) hlt
      have hs : 0 < Nat.size (k + 1) := Nat.size_pos.mpr (Nat.succ_pos k)
      have hup : (k + 1) < 2 ^ Nat.size (k + 1) := Nat.lt_size_self _
      have hhalf : (k + 1) / 2 < 2 ^ (Nat.size (k + 1) - 1) := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        calc (k + 1) < 2 ^ Nat.size (k + 1) := hup
          _ = 2 ^ (Nat.size (k + 1) - 1) * 2 := by
              rw [← pow_succ]
              congr 1
              omega
      have hsize : Nat.size ((k + 1) / 2) ≤ Nat.size (k + 1) - 1 :=
        Nat.size_le.mpr hhalf
      rw [powModSteps]
      omega
