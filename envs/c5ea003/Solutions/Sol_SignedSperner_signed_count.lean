-- Prove2me | solution 1 for SignedSperner.signed_count
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:00:04.491338+00:00
-- url     : https://prove2.me/submissions/21a95118-591b-4725-aa56-c4435296a53e

-- Sol generated from Novelty/SignedSperner.lean
import Mathlib
import Definitions.Def_Novelty_SignedSperner

/-!
# The 1-D Sperner lemma as an exact signed count (a discrete degree)

The earlier work established the *parity* form of the one–dimensional Sperner lemma:
the number of "fully coloured" edges of a two–colouring of the path `0, 1, …, n` has
a fixed parity determined by the endpoints.  This file **deepens** that result from a
statement modulo `2` to an *exact integer identity*, by separating fully coloured
edges into **oriented** ones:

* an *up*-edge is a `false → true` transition (`upCount`), and
* a *down*-edge is a `true → false` transition (`downCount`).

The main theorem is a telescoping identity — the discrete analogue of "the degree of
a boundary map":

> **Signed Sperner count.**  `upCount c n - downCount c n = ⟦c n⟧ - ⟦c 0⟧`,
> where `⟦·⟧` sends `false ↦ 0`, `true ↦ 1`.

Every classical consequence drops out as a *corollary* of this single identity:

* the parity form (`parity`), recovering the earlier result;
* balanced crossings when the endpoints agree (`upCount_eq_downCount_of_eq`);
* Sperner existence, oriented (`exists_oriented`) and unoriented
  (`exists_fullyColoured_of_ne`);
* two discrete intermediate–value theorems (`discrete_ivt`, `discrete_ivt'`); and
* a discrete Brouwer fixed–point statement (`discrete_brouwer`) — the combinatorial
  bridge from Sperner to Brouwer, and hence to the existence of equilibria.

## Main results

* `SignedSperner.signed_count` — the exact signed identity (the flagship).
* `SignedSperner.card_eq` — `fullyColoured` splits into up- and down-edges.
* `SignedSperner.parity` — the parity form, as a corollary.
* `SignedSperner.upCount_eq_downCount_of_eq` — equal endpoints ⇒ equal crossings.
* `SignedSperner.exists_oriented`, `SignedSperner.exists_fullyColoured_of_ne` —
  Sperner existence.
* `SignedSperner.discrete_ivt`, `SignedSperner.discrete_ivt'` — discrete IVTs.
* `SignedSperner.discrete_brouwer` — a discrete Brouwer fixed point.
-/

open SignedSperner

open Finset















open SignedSperner in
theorem solution(c : ℕ → Bool) (n : ℕ) :
    (upCount c n : ℤ) - downCount c n = boolVal (c n) - boolVal (c 0) := by
  unfold upCount downCount
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  have key : ∀ i, ((if c i = false ∧ c (i + 1) = true then (1 : ℤ) else 0)
      - (if c i = true ∧ c (i + 1) = false then 1 else 0))
      = boolVal (c (i + 1)) - boolVal (c i) := by
    intro i; unfold boolVal
    cases hi : c i <;> cases hi1 : c (i + 1) <;> simp
  simp_rw [key]
  exact Finset.sum_range_sub (fun i => boolVal (c i)) n
