-- Prove2me | solution 1 for QSPoolKernel.card_ker_sqUnits
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:16:01.554784+00:00
-- url     : https://prove2.me/submissions/f77c634c-ffc3-43fc-ba5c-bd009829ed5d

-- Sol generated from Shared/QSPoolKernelSymmetry.lean
import Mathlib
import Definitions.Def_Shared_QSPoolKernelSymmetry
import Definitions.Def_Shared_QSRelationPoolRandom
import Theorems.Thm_QSPoolKernel_mem_ker_sqUnits_iff

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
theorem solution(hp : p ≠ 2) :
    Nat.card (MonoidHom.ker (sqUnits p)) = 2 := by
  have hcoe : ((MonoidHom.ker (sqUnits p) : Subgroup (ZMod p)ˣ) : Set (ZMod p)ˣ)
      = {1, -1} := by
    ext u
    simpa using mem_ker_sqUnits_iff (p := p) (u := u)
  have hp2 : 2 < p := lt_of_le_of_ne (Fact.out (p := p.Prime)).two_le (Ne.symm hp)
  haveI : Fact (2 < p) := ⟨hp2⟩
  have hne : (1 : (ZMod p)ˣ) ≠ -1 := by
    intro h
    have h1 : (1 : ZMod p) = -1 := by
      simpa using congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) h
    exact (ZMod.neg_one_ne_one (n := p)) h1.symm
  calc Nat.card (MonoidHom.ker (sqUnits p))
      = Nat.card ({1, -1} : Set (ZMod p)ˣ) := Nat.card_congr (Equiv.setCongr hcoe)
    _ = 2 := by rw [Nat.card_coe_set_eq, Set.ncard_pair hne]
