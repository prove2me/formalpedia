-- Prove2me | Definitions.Def_Novelty_SignedSperner
-- name    : Novelty_SignedSperner
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:17.857228+00:00
-- url     : https://prove2.me/theorems/e88d6d52-8d1f-44fe-8882-cd5e0011eb4c
-- title:
--   Aether Catalog definitions — Novelty_SignedSperner
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SignedSperner`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SignedSperner.lean by skeleton subtraction
import Mathlib

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

namespace SignedSperner

open Finset

/-- The Boolean colour value: `false ↦ 0`, `true ↦ 1`. -/
def boolVal (b : Bool) : ℤ := if b then 1 else 0

/-- The number of *up*-edges (`false → true` transitions) among `0, …, n-1`. -/
def upCount (c : ℕ → Bool) (n : ℕ) : ℕ :=
  ((range n).filter (fun i => c i = false ∧ c (i + 1) = true)).card

/-- The number of *down*-edges (`true → false` transitions) among `0, …, n-1`. -/
def downCount (c : ℕ → Bool) (n : ℕ) : ℕ :=
  ((range n).filter (fun i => c i = true ∧ c (i + 1) = false)).card

/-- The set of *fully coloured* edges (endpoints of different colour). -/
def fullyColoured (c : ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (range n).filter (fun i => c i ≠ c (i + 1))










end SignedSperner


