-- Prove2me | Definitions.Def_Shared_QSPoolKernelSymmetry
-- name    : Shared_QSPoolKernelSymmetry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:06:27.509493+00:00
-- url     : https://prove2.me/theorems/cb03085c-f175-4a49-9b76-ad34ebb83b7c
-- title:
--   Aether Catalog definitions — Shared_QSPoolKernelSymmetry
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.QSPoolKernelSymmetry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/QSPoolKernelSymmetry.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_QSRelationPoolRandom

/-!
# Why the two factors of two cancel: they are the same `2`

`Catalog.Shared.QSRelationPoolRandom` proves the numerical cancellation that
explains the measured random-equivalence of the quadratic-sieve relation pool:
only `(p-1)/2` residues `N` admit a relation modulo `p`, but each admissible one
is hit by `2` residues `x` per period, so the expected number of hits per period
is exactly `1`, as for a random integer sequence.

This file identifies the *structural* reason.  Both factors of `2` are the order
of the kernel of the squaring endomorphism of `(ZMod p)ˣ`, i.e. the group
`{1, -1}`:

* the fibre of the squaring map is a coset of `{±1}`, which is why an admissible
  prime hits twice (`sqrt_set_eq_pair`, `rootCount_eq_card_ker`);
* the image of the squaring map has index `|{±1}| = 2`, which is why only half
  the residues are admissible (`card_ker_mul_card_admissible`).

So the "quadratic-character constraint" and the "doubled hit density" are two
faces of the single `Z/2` symmetry `x ↦ -x` of the sieve polynomial `x^2 - N`,
and their product is forced to be `1` by the orbit–stabiliser identity.  No
amount of extra scale can create a discrepancy: the cancellation is an identity,
not an asymptotic.

Main results:

* `neg_ne_self_of_ne_zero` — the `Z/2` action `x ↦ -x` on roots is free.
* `sqrt_set_eq_pair` — a fibre of squaring is exactly `{x, -x}`.
* `card_ker_sq` — the kernel of `u ↦ u^2` on `(ZMod p)ˣ` has order `2`.
* `rootCount_eq_card_ker` — the local hit count of an admissible modulus is the
  kernel order.
* `card_ker_mul_card_admissible` — kernel order times number of admissible
  residues is `|(ZMod p)ˣ|`: the exact orbit–stabiliser cancellation.
* `pool_expected_hits_eq_random` — final form: the pool's expected hit count per
  period equals the random model's, exactly, at every prime.
-/

namespace QSPoolKernel

open Finset QSRelationPool

variable {p : ℕ} [Fact p.Prime]



/-- The squaring endomorphism of the unit group. -/
noncomputable def sqUnits (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* (ZMod p)ˣ :=
  powMonoidHom 2






end QSPoolKernel


