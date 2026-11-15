-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:53.122667+00:00
-- url     : https://prove2.me/submissions/6abc4d6b-08c5-4422-aa23-aa3e8d72f80f

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/

namespace Wikipedia.SzemeredisTheorem



@[simp]
theorem mem_greenTaoInterval {N n : ℕ} :
    n ∈ greenTaoInterval N ↔ N / 64 ≤ n ∧ n ≤ N / 4 := by
  simp [greenTaoInterval]























end Wikipedia.SzemeredisTheorem

end
/-!
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
theorem solution {N : ℕ} [NeZero N]
    {α : ℝ} (hα : 0 < α) {W : ℕ} (hW : 0 < W)
    (b : ℕ) (n : ZMod N) :
    0 < wTrickedPrimeWeight α W b n ↔
      n.val ∈ greenTaoInterval N ∧
        Nat.Prime (wTrickedValue W b n) := by
  by_cases h :
      n.val ∈ greenTaoInterval N ∧
        Nat.Prime (wTrickedValue W b n)
  · rw [wTrickedPrimeWeight, if_pos h]
    constructor
    · intro
      exact h
    · intro
      have htotient : 0 < (W.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hW
      have hWreal : 0 < (W : ℝ) := by
        exact_mod_cast hW
      have hpReal : 1 < (wTrickedValue W b n : ℝ) := by
        exact_mod_cast h.2.one_lt
      exact mul_pos (mul_pos hα (div_pos htotient hWreal))
        (Real.log_pos hpReal)
  · rw [wTrickedPrimeWeight, if_neg h]
    simpa using h
