-- Prove2me | Definitions.Def_Bridges_TuranExplicitCount
-- name    : Bridges_TuranExplicitCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:09.177896+00:00
-- url     : https://prove2.me/theorems/2b520944-bb15-4be7-a3b2-c0491f9ecec2
-- title:
--   Aether Catalog definitions — Bridges_TuranExplicitCount
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TuranExplicitCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TuranExplicitCount.lean by skeleton subtraction
import Mathlib
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

namespace TuranExplicitCount

variable {n r : ℕ}

/-! ## Residue classes in `Fin n` -/


/-! ## The Turán graph is regular, and its edge count -/




/-! ## The general (non-divisible) edge count of the Turán graph -/

/-- The number of vertices of `Fin n` in the residue class `i` mod `r`. -/
def classSize (n r i : ℕ) : ℕ :=
  #((univ : Finset (Fin n)).filter (fun w : Fin n => (w : ℕ) % r = i))




/-! ## Turán's theorem, quantitatively -/



end TuranExplicitCount


