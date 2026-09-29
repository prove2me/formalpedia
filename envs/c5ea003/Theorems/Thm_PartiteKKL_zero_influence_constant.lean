-- Prove2me | Theorems.Thm_PartiteKKL_zero_influence_constant
-- name    : PartiteKKL.zero_influence_constant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:19:46.275724+00:00
-- url     : https://prove2.me/theorems/d7755fc3-67f7-4097-ab9c-8342a1343cc9
-- title:
--   Vanishing-influence boundary of KKL.
-- statement:
--   **Vanishing-influence boundary of KKL.**  A facet-labelling all of whose colour
--   influences vanish is constant.  Hence the KKL conclusion (an influential
--   coordinate) can fail only for the degenerate constant labellings — the exact
--   boundary case that the local-to-global theorem excludes via its lower-bound
--   hypotheses.
--
--   ```lean
--   theorem PartiteKKL.zero_influence_constant{n m : ℕ} (f : (Fin n → Fin m) → Bool)
--       (h : ∀ i, Inf f i = 0) (x y : Fin n → Fin m) : f x = f y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/LocalToGlobalKKLConnector.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/LocalToGlobalKKLConnector.lean#L308

-- Thm stub generated from Novelty/LocalToGlobalKKLConnector.lean
import Mathlib
import Definitions.Def_Novelty_LocalToGlobalKKLConnector

/-!
# A Local-to-Global KKL Theorem for Partite Simplicial Complexes over an Arbitrary Alphabet

This file develops a *local-to-global* principle for coordinate influences on the
complete `n`-partite simplicial complex whose colour classes each have `m`
vertices, in the spirit of the Kahn–Kalai–Linial (KKL) influence theorem and the
high-dimensional-expander "local-to-global" machinery (Kahn–Kalai–Linial 1988;
Bafna–Hoory–Kaufman 2022; Gur–Lifshitz–Liu 2022; Gotlib–Kaufman 2023).

## The complex and its links

The facets (top-dimensional simplices) of the complete `n`-partite complex with
parts of size `m` are exactly the *transversals*: functions `x : Fin n → Fin m`
choosing one vertex from each colour class.  A Boolean labelling of the facets is a
function `f : (Fin n → Fin m) → Bool`.

For a colour `i`, two facets are **`i`-adjacent** when they agree on every colour
`k ≠ i` and differ at colour `i`.  The (unnormalised) **influence** `Inf f i`
counts the ordered `i`-adjacent facet pairs on which `f` changes value — the edges
of the `i`-th Hamming direction that are sensitive for `f`.

Pinning colour `j` to a vertex `b` cuts out the **link** of that vertex: the
subcomplex of facets `x` with `x j = b`.  `InfSub f j b i` counts the sensitive
`i`-edges lying inside that link.

The Boolean cube studied classically is the special case `m = 2`; here every
vertex has `m` links rather than two.

## Results

* `inf_decomp` — the **self-averaging bridge**: every global influence splits as
  the sum of the influences over the `m` links of any fixed colour,
  `Inf f i = ∑ b, InfSub f j b i`.
* `linktot_decomp` — summing the bridge over colours gives the local-to-global
  decomposition of the total influence.
* `localToGlobal_KKL_partite` — the flagship statement: if all `m` links of a
  colour `j` carry link-influence at least `T` (the *local* KKL hypothesis on each
  link), then some global colour `i ≠ j` has influence at least the average
  `mT/(n-1)`.
* `abstract_localToGlobal_KKL` / `abstract_global_influential_coord` — the abstract
  weighted-averaging engine behind every such argument, and
  `partite_total_via_abstract` exhibiting the partite complex as an instance.
* `partite_localKKL_influential_coord_real` — the real-valued averaged form.
* `zero_influence_constant` — the exact converse boundary: a labelling all of whose
  colour influences vanish is constant, so the KKL conclusion is vacuous precisely
  for the degenerate (constant) labellings.
-/

open PartiteKKL

open Finset

/-! ## The complete `n`-partite complex over the alphabet `Fin m` -/


variable {n m : ℕ}









/-! ### Pigeonhole -/





/-! ## Abstract engine: local KKL ⟹ global KKL -/







/-! ## The partite complex as an instance of the abstract engine -/


/-! ## Real-valued averaged global influential coordinate -/


/-! ## The degenerate boundary: vanishing influence forces constancy -/

theorem PartiteKKL.zero_influence_constant{n m : ℕ} (f : (Fin n → Fin m) → Bool)
    (h : ∀ i, Inf f i = 0) (x y : Fin n → Fin m) : f x = f y := by sorry
