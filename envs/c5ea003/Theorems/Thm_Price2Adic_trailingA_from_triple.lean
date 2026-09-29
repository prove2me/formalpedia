-- Prove2me | Theorems.Thm_Price2Adic_trailingA_from_triple
-- name    : Price2Adic.trailingA_from_triple
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:57:46.013476+00:00
-- url     : https://prove2.me/theorems/d9260060-f213-4519-a246-0f25f6b5fbb7
-- title:
--   Triple-level `A`-run law.
-- statement:
--   **Triple-level `A`-run law.**  For a node with triple `(a, b, c)`, the trailing
--   `A`-run of its Price address is `v₂(b) - 1` when `a ≡ 1 (mod 4)` and `0` when
--   `a ≡ 3 (mod 4)`: the run is read off the even leg alone, with the mod-4 class of the odd
--   leg deciding whether the reading applies.
--
--   ```lean
--   theorem Price2Adic.trailingA_from_triple(p : ℕ × ℕ) (hp : Valid p) :
--       trailingA (address p) =
--         (if oddLeg p % 4 = 1 then padicValNat 2 (triple p).2.1 - 1 else 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/Price2Adic/Runs.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/Price2Adic/Runs.lean#L84

-- Thm stub generated from Cryptography/Price2Adic/Runs.lean
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Runs
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

open Price2Adic

theorem Price2Adic.trailingA_from_triple(p : ℕ × ℕ) (hp : Valid p) :
    trailingA (address p) =
      (if oddLeg p % 4 = 1 then padicValNat 2 (triple p).2.1 - 1 else 0) := by sorry
