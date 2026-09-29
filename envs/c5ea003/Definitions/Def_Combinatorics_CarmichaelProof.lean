-- Prove2me | Definitions.Def_Combinatorics_CarmichaelProof
-- name    : Combinatorics_CarmichaelProof
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:28:58.959448+00:00
-- url     : https://prove2.me/theorems/497e759f-cb74-41ff-bec9-3edecb088a8d
-- title:
--   Aether Catalog definitions — Combinatorics_CarmichaelProof
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.CarmichaelProof`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/CarmichaelProof.lean by skeleton subtraction
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


