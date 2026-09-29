-- Prove2me | Definitions.Def_Cryptography_Price2Adic_Runs
-- name    : Cryptography_Price2Adic_Runs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:22:42.079197+00:00
-- url     : https://prove2.me/theorems/20482cb3-09bd-498e-a7d9-f5f5d9f252b6
-- title:
--   Aether Catalog definitions — Cryptography_Price2Adic_Runs
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.Price2Adic.Runs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/Price2Adic/Runs.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Tree

/-!
# The trailing `A`-run is a 2-adic valuation

`Letters.lean` showed that `N mod 4` and `N mod 8` read the last two letters of a Price
address and that no 2-adic residue reads more.  This file identifies what the *whole*
2-adic filtration does read: the length of the terminal block of `A`'s.

* `trailingA_eq_padicValNat` — for every Price word `w`, the number of trailing `A`'s of
  `w` equals `v₂(n)`, the 2-adic valuation of the smaller Euclid parameter of the node
  `eval w`.  The halving alphabet is literally a 2-adic valuation counter.
* `trailingA_address` — the same statement read off a node.
* `trailingA_from_triple` — the triple-level form: the trailing `A`-run of the address of
  a node with triple `(a, b, c)` is `v₂(b) - 1` when `a ≡ 1 (mod 4)`, and `0` when
  `a ≡ 3 (mod 4)`.  Everything is observable from the triple, with no reference to the
  Euclid parameters.

Combined with `twoAdic_blind_BC`, this is the exact 2-adic content of a Price address:
the terminal `A`-run, and nothing else.

## Lab notes (round 70, exp 548)

BFS to depth `8`: for all `9841` nodes the trailing-`A` count matched `v₂(n)` and
matched `v₂(b) - 1` whenever the odd leg was `1 mod 4` (`0` otherwise), with no
exceptions.  Root case: address `[]`, `n = 1`, `v₂ = 0`.
-/

namespace Price2Adic

/-- The number of trailing `A`'s of a Price word. -/
def trailingA (w : PriceWord) : ℕ :=
  (w.reverse.takeWhile (fun l => decide (l = .A))).length











end Price2Adic


