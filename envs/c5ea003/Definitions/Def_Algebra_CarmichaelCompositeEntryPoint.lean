-- Prove2me | Definitions.Def_Algebra_CarmichaelCompositeEntryPoint
-- name    : Algebra_CarmichaelCompositeEntryPoint
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:08:34.656162+00:00
-- url     : https://prove2.me/theorems/5429fd7a-d9be-4e00-beec-8f78c637fcc9
-- title:
--   Aether Catalog definitions — Algebra_CarmichaelCompositeEntryPoint
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.CarmichaelCompositeEntryPoint`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/CarmichaelCompositeEntryPoint.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_PosetTheory_FibonacciApparitionSheaf

/-! # Entry points and primitive Fibonacci divisors

The entry point of a prime is its least positive Fibonacci index of apparition.
This file derives its divisibility and primitivity properties from the general
rank-of-apparition theory.
-/

open Nat
open FibonacciApparitionSheaf

/-- The Fibonacci entry point of a prime. -/
noncomputable def entryPoint (p : ℕ) : ℕ := fibRank p

/-- A number `e` is the Fibonacci entry point of `p`. -/
def IsFibEntry (p e : ℕ) : Prop :=
  0 < e ∧ p ∣ Nat.fib e ∧ ∀ k, 0 < k → k < e → ¬ p ∣ Nat.fib k

/-- A prime is primitive at index `n` if it divides `F n` but no earlier positive value. -/
def FibPrimitivePrimeAt (n p : ℕ) : Prop :=
  Nat.Prime p ∧ p ∣ Nat.fib n ∧ ∀ k, 0 < k → k < n → ¬ p ∣ Nat.fib k


