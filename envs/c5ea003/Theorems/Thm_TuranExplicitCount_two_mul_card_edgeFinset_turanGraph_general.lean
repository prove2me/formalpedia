-- Prove2me | Theorems.Thm_TuranExplicitCount_two_mul_card_edgeFinset_turanGraph_general
-- name    : TuranExplicitCount.two_mul_card_edgeFinset_turanGraph_general
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:22:25.346451+00:00
-- url     : https://prove2.me/theorems/c9bb77b1-bff4-42e6-adf8-27ea36e7b410
-- title:
--   The edge count of the Turán graph, in general.
-- statement:
--   **The edge count of the Turán graph, in general.**  `2 · #edges + ∑_i |class i|² = n²`, with no
--   divisibility hypothesis; when `r ∣ n` all classes have size `n/r` and this specializes to
--   `two_mul_card_edgeFinset_turanGraph`.
--
--   ```lean
--   theorem TuranExplicitCount.two_mul_card_edgeFinset_turanGraph_general(hr : 0 < r) :
--       2 * #(turanGraph n r).edgeFinset + ∑ i ∈ range r, (classSize n r i) ^ 2 = n ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TuranExplicitCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TuranExplicitCount.lean#L161

-- Thm stub generated from Bridges/TuranExplicitCount.lean
import Mathlib
import Definitions.Def_Bridges_TuranExplicitCount
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge: the explicit Turán construction ↔ the quantitative extremal bound

Mathlib knows the *structural* Turán theorem: `SimpleGraph.isTuranMaximal_turanGraph` says the
Turán graph `turanGraph n r` (vertices `Fin n`, adjacency `v % r ≠ w % r`) maximises the number
of edges among `K_{r+1}`-free graphs, and `isTuranMaximal_iff_nonempty_iso_turanGraph` says it is
the unique such maximiser.  What Mathlib does *not* record is the **number**
`(1 - 1/r) · n² / 2`.

This file supplies exactly that missing quantitative half, by counting the explicit
construction rather than by any extremal/probabilistic argument:

* `card_residue_class` : when `r ∣ n`, each residue class mod `r` inside `Fin n` has exactly
  `n / r` elements.
* `turanGraph_degree` : hence `turanGraph n r` is `(n - n/r)`-regular.
* `two_mul_card_edgeFinset_turanGraph` : `2 · #edges (turanGraph n r) = n · (n - n/r)`, via the
  handshake lemma.
* `card_edgeFinset_turanGraph_real` : `#edges (turanGraph n r) = (1 - 1/r) · n² / 2` in `ℝ`.
* `turan_bound_real` : every `K_{r+1}`-free graph on `Fin n` has at most `(1 - 1/r) · n² / 2`
  edges (`r ∣ n`), and `turan_extremal_number` states this bound is *attained*, i.e. it is the
  extremal number: an `IsGreatest` statement.

The bridge is: an existence/optimality theorem (Mathlib's `IsTuranMaximal`) is converted into a
closed-form arithmetic value by evaluating an explicit combinatorial construction.

## Catalog connections
* `Bridges/GenTuranAsymptoticBridge.lean` : generalized Turán counting; this file provides the
  classical `r`-partite case with the exact constant.
* `Bridges/ErdosProbabilisticRamsey.lean` : the other half of the probabilistic-method trio.
-/

open Finset SimpleGraph

open TuranExplicitCount

variable {n r : ℕ}

/-! ## Residue classes in `Fin n` -/


/-! ## The Turán graph is regular, and its edge count -/




/-! ## The general (non-divisible) edge count of the Turán graph -/

theorem TuranExplicitCount.two_mul_card_edgeFinset_turanGraph_general(hr : 0 < r) :
    2 * #(turanGraph n r).edgeFinset + ∑ i ∈ range r, (classSize n r i) ^ 2 = n ^ 2 := by sorry
