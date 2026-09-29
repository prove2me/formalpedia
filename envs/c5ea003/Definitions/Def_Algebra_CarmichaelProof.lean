-- Prove2me | Definitions.Def_Algebra_CarmichaelProof
-- name    : Algebra_CarmichaelProof
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:08:25.156171+00:00
-- url     : https://prove2.me/theorems/3c861f31-45cc-4755-ab3e-011e17db9f53
-- title:
--   Aether Catalog definitions — Algebra_CarmichaelProof
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.CarmichaelProof`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/CarmichaelProof.lean by skeleton subtraction
import Mathlib

/-! # Certified finite range of Carmichael's theorem (composite case)

We prove that every composite `n` with `13 ≤ n ≤ 10000` gives `F(n)` a
primitive prime divisor.
-/

set_option maxHeartbeats 800000

/-! ## Bridge Lemma -/


/-! ## Computational verification infrastructure -/

/-- Strip all factors of m from r, with bounded fuel -/
def stripAllAux (r : ℕ) (m : ℕ) : ℕ → ℕ
  | 0 => r
  | fuel + 1 =>
    if m ≤ 1 then r
    else
      let g := Nat.gcd r m
      if g ≤ 1 then r
      else stripAllAux (r / g) m fuel

/-- List of proper divisors of n (d with 0 < d < n and d | n) -/
def propDivs (n : ℕ) : List ℕ :=
  (List.range n).filter fun d => 0 < d && d < n && n % d == 0

/-- The primitive part of F(n) -/
def primPart (n : ℕ) : ℕ :=
  let fn := Nat.fib n
  (propDivs n).foldl (fun r d => stripAllAux r (Nat.fib d) r) fn

/-! ## Correctness lemmas -/






/-! ## Computational verification -/


/-! ## The composite case -/


