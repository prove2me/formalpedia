-- Prove2me | Theorems.Thm_PartiteKKL_partite_total_via_abstract
-- name    : PartiteKKL.partite_total_via_abstract
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:19:29.638735+00:00
-- url     : https://prove2.me/theorems/25c37864-84f7-44c4-b994-99e05fe457b7
-- title:
--   The partite decomposition is an instance of the abstract engine.
-- statement:
--   **The partite decomposition is an instance of the abstract engine.**  Taking the
--   `m` links of colour `j` as a family of unit weight recovers the total-influence
--   lower bound: if each link has an influential coordinate of influence at least `T`,
--   then the total influence of `f` is at least `mT`.
--
--   ```lean
--   theorem PartiteKKL.partite_total_via_abstract{n m : ℕ} (f : (Fin n → Fin m) → Bool) (j : Fin n)
--       (T : ℕ) (hlink : ∀ b : Fin m, ∃ i, T ≤ InfSub f j b i) :
--       (m : ℝ) * T ≤ TotInf f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/LocalToGlobalKKLConnector.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/LocalToGlobalKKLConnector.lean#L235

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

theorem PartiteKKL.partite_total_via_abstract{n m : ℕ} (f : (Fin n → Fin m) → Bool) (j : Fin n)
    (T : ℕ) (hlink : ∀ b : Fin m, ∃ i, T ≤ InfSub f j b i) :
    (m : ℝ) * T ≤ TotInf f := by sorry
