-- Prove2me | Definitions.Def_Applications_CarmichaelCompositeEntryPoint
-- name    : Applications_CarmichaelCompositeEntryPoint
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:07.128288+00:00
-- url     : https://prove2.me/theorems/2e53722f-20a5-4da6-8de4-a2e4f37ba788
-- title:
--   Aether Catalog definitions — Applications_CarmichaelCompositeEntryPoint
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CarmichaelCompositeEntryPoint`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CarmichaelCompositeEntryPoint.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_Pythagorean_RankOfApparition

/-! # Entry points and primitive Fibonacci divisors

The entry point of a prime is its least positive Fibonacci index of apparition.
This file derives its divisibility and primitivity properties from the general
rank-of-apparition theory.
-/

open Nat
open RankOfApparition

/-- The Fibonacci entry point of a prime. -/
noncomputable def entryPoint (p : ℕ) : ℕ := fibRank p

/-- A number `e` is the Fibonacci entry point of `p`. -/
def IsFibEntry (p e : ℕ) : Prop :=
  0 < e ∧ p ∣ Nat.fib e ∧ ∀ k, 0 < k → k < e → ¬ p ∣ Nat.fib k

/-- A prime is primitive at index `n` if it divides `F n` but no earlier positive value. -/
def FibPrimitivePrimeAt (n p : ℕ) : Prop :=
  Nat.Prime p ∧ p ∣ Nat.fib n ∧ ∀ k, 0 < k → k < n → ¬ p ∣ Nat.fib k


