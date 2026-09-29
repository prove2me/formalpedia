-- Prove2me | Definitions.Def_Cryptography_Price2Adic_Counting
-- name    : Cryptography_Price2Adic_Counting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:22:17.992427+00:00
-- url     : https://prove2.me/theorems/bbe3bb50-da96-4eee-bc82-c0557ed10e1e
-- title:
--   Aether Catalog definitions — Cryptography_Price2Adic_Counting
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.Price2Adic.Counting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/Price2Adic/Counting.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Tree

/-!
# Counting: the Price tree certifies exponentially many primitive triples

The bijection `evalEquiv` of `Tree.lean` is qualitative.  This file extracts its
quantitative consequence, using the depth bound `sum_le_of_length`:

* `card_valid_ge` — for every `d`, there are at least `3^d` primitive Euclid parameter
  pairs with `m + n ≤ 3^(d+1)`; i.e. the counting function of primitive Pythagorean
  triples ordered by `m+n` is at least `3^d` at `3^(d+1)`.

The proof is the Price tree itself: the `3^d` words of length `d` give `3^d` distinct
nodes (uniqueness) all of parameter sum at most `3^(d+1)` (the geometric depth bound).
-/

namespace Price2Adic

open Finset

instance : Fintype PriceLetter where
  elems := {.A, .B, .C}
  complete := by intro l; cases l <;> simp


/-- The nodes of depth `d`, as a finite set of parameter pairs. -/
noncomputable def depthNodes (d : ℕ) : Finset (ℕ × ℕ) :=
  (univ : Finset (Fin d → PriceLetter)).image (fun g => eval (List.ofFn g))




end Price2Adic


