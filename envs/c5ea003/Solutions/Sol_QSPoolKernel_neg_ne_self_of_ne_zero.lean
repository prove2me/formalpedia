-- Prove2me | solution 1 for QSPoolKernel.neg_ne_self_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:16:02.371985+00:00
-- url     : https://prove2.me/submissions/8d32eeff-3c46-4411-ad63-f8dbc338d234

-- Sol generated from Shared/QSPoolKernelSymmetry.lean
import Mathlib
import Definitions.Def_Shared_QSPoolKernelSymmetry
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

open QSPoolKernel

open Finset QSRelationPool

variable {p : ℕ} [Fact p.Prime]










open QSPoolKernel in
theorem solution(hp : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : -x ≠ x := by
  intro h
  have h2 : (2 : ZMod p) * x = 0 := by
    have : x + x = 0 := by
      calc x + x = -x + x := by rw [h]
        _ = 0 := by ring
    linear_combination this
  rcases mul_eq_zero.1 h2 with h3 | h3
  · have hdvd : (p : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h3)
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out (p := p.Prime)).two_le
    omega
  · exact hx h3
