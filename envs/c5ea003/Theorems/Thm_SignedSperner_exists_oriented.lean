-- Prove2me | Theorems.Thm_SignedSperner_exists_oriented
-- name    : SignedSperner.exists_oriented
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:30:37.423597+00:00
-- url     : https://prove2.me/theorems/1964ff96-6784-40fb-834b-6bc40be796a1
-- title:
--   Oriented Sperner existence.
-- statement:
--   **Oriented Sperner existence.**  A Sperner colouring (`c 0 = false`,
--   `c n = true`) has an oriented fully coloured edge: some `i < n` with `c i = false`
--   and `c (i+1) = true`.
--
--   ```lean
--   theorem SignedSperner.exists_oriented(c : ℕ → Bool) (n : ℕ) (h0 : c 0 = false) (hn : c n = true) :
--       ∃ i < n, c i = false ∧ c (i + 1) = true := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SignedSperner.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SignedSperner.lean#L109

-- Thm stub generated from Novelty/SignedSperner.lean
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

theorem SignedSperner.exists_oriented(c : ℕ → Bool) (n : ℕ) (h0 : c 0 = false) (hn : c n = true) :
    ∃ i < n, c i = false ∧ c (i + 1) = true := by sorry
