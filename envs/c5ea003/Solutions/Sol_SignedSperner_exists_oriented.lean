-- Prove2me | solution 1 for SignedSperner.exists_oriented
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:03:13.613561+00:00
-- url     : https://prove2.me/submissions/ec1b8272-44ef-40ec-8018-93d42eac4ecf

-- Sol generated from Novelty/SignedSperner.lean
import Mathlib
import Definitions.Def_Novelty_SignedSperner
import Theorems.Thm_SignedSperner_signed_count

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
theorem solution(c : ℕ → Bool) (n : ℕ) (h0 : c 0 = false) (hn : c n = true) :
    ∃ i < n, c i = false ∧ c (i + 1) = true := by
  have h1 := signed_count c n
  rw [h0, hn] at h1
  have hup : 0 < upCount c n := by
    have := h1
    simp only [boolVal] at this
    norm_num at this
    omega
  unfold upCount at hup
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hup
  rw [Finset.mem_filter, Finset.mem_range] at hi
  exact ⟨i, hi.1, hi.2⟩
