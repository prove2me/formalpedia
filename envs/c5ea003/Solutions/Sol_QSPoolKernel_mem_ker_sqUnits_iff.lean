-- Prove2me | solution 1 for QSPoolKernel.mem_ker_sqUnits_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:14:44.662655+00:00
-- url     : https://prove2.me/submissions/bf62b3e7-d944-4044-9c5d-831dff09243e

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
theorem solution{u : (ZMod p)ˣ} :
    u ∈ MonoidHom.ker (sqUnits p) ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro hu
    have hu' : (u : ZMod p) ^ 2 = 1 := by
      have := MonoidHom.mem_ker.1 hu
      simpa [sqUnits, powMonoidHom] using congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) this
    have h : ((u : ZMod p) - 1) * ((u : ZMod p) + 1) = 0 := by linear_combination hu'
    rcases mul_eq_zero.1 h with h1 | h1
    · left
      apply Units.ext
      have : (u : ZMod p) = 1 := by linear_combination h1
      simpa using this
    · right
      apply Units.ext
      have : (u : ZMod p) = -1 := by linear_combination h1
      simpa using this
  · rintro (rfl | rfl) <;> simp [MonoidHom.mem_ker, sqUnits, powMonoidHom]
