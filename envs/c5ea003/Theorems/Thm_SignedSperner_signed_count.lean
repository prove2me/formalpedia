-- Prove2me | Theorems.Thm_SignedSperner_signed_count
-- name    : SignedSperner.signed_count
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:31:13.45316+00:00
-- url     : https://prove2.me/theorems/ef44f19d-695e-4334-bfc2-e9d12f021816
-- title:
--   Signed Sperner count (flagship).
-- statement:
--   **Signed Sperner count (flagship).**  Along the path `0, 1, …, n`, the number of
--   `false → true` edges minus the number of `true → false` edges equals the difference
--   of the endpoint colour values.  This telescoping identity is the exact 1-D Sperner
--   lemma; the parity form is a corollary.
--
--   ```lean
--   theorem SignedSperner.signed_count(c : ℕ → Bool) (n : ℕ) :
--       (upCount c n : ℤ) - downCount c n = boolVal (c n) - boolVal (c 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SignedSperner.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SignedSperner.lean#L61

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

theorem SignedSperner.signed_count(c : ℕ → Bool) (n : ℕ) :
    (upCount c n : ℤ) - downCount c n = boolVal (c n) - boolVal (c 0) := by sorry
