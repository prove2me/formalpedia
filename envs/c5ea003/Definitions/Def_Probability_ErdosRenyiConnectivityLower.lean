-- Prove2me | Definitions.Def_Probability_ErdosRenyiConnectivityLower
-- name    : Probability_ErdosRenyiConnectivityLower
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:44:58.219994+00:00
-- url     : https://prove2.me/theorems/aa3eb200-756d-43b7-a673-a7644034f1d3
-- title:
--   Aether Catalog definitions — Probability_ErdosRenyiConnectivityLower
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ErdosRenyiConnectivityLower`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ErdosRenyiConnectivityLower.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_ErdosRenyiThreshold
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The subcritical half of the connectivity threshold for `G(n,p)`

This file proves the "zero side" of the sharp connectivity threshold for the
Erdős–Rényi random graph: **below** the density `log n / n` the random graph
`G(n,p)` is a.a.s. *disconnected*.

We build directly on the finite `G(n,p)` model of `Probability.ErdosRenyiThreshold`
(configurations are finsets of potential edges, `mass`/`Prob`/`Expect`/`Variance`),
adding the two ingredients that were missing there:

* the **avoidance** (all-absent) probability `Prob p {s | Disjoint s T} = (1-p)^|T|`,
  obtained from the already-proved containment probability by the complementation
  duality `mass p sᶜ = mass (1-p) s`;
* the **exact second moment** of a count of avoided edge-blocks,
  `E[X²] = ∑ i ∑ j (1-p)^{|Bᵢ ∪ Bⱼ|}`.

Specialising the blocks `B v` to the stars `incident v` (all edges at a vertex `v`)
turns `X` into the number of **isolated vertices**, whose first two moments are
`E X = n (1-p)^{n-1}` and `E X² = n (1-p)^{n-1} + n(n-1)(1-p)^{2n-3}`.  Chebyshev's
inequality (`prob_eq_zero_le_variance_div_sq`, already available) then gives the
clean quantitative bound

`P(G(n,p) is connected) ≤ 1 / (n (1-p)^{n-1}) + p/(1-p)`,

and hence `P(connected) → 0` whenever `p → 0` and the expected number of isolated
vertices `n (1-p)^{n-1} → ∞`.  Both hypotheses hold for `p = c·log n / n` with
`0 < c < 1`, which is the classical statement that `log n / n` is the connectivity
threshold from below.
-/

open Finset BigOperators Filter Topology
open scoped Classical

namespace ErdosRenyi

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## 1. Avoidance probabilities -/




/-! ## 2. Counting avoided blocks and its second moment -/

/-- The number of blocks `B i` that are entirely absent from the configuration `s`. -/
noncomputable def avoidCount {ι : Type*} [Fintype ι] (B : ι → Finset α) (s : Finset α) : ℝ :=
  ∑ i : ι, if Disjoint s (B i) then (1 : ℝ) else 0




/-! ## 3. The isolated-vertex count in `G(n,p)` -/

/-- The star at `v`: all potential edges incident to the vertex `v`. -/
noncomputable def incident {n : ℕ} (v : Fin n) : Finset (Edge n) :=
  Finset.univ.filter (fun e => v ∈ (e : Sym2 (Fin n)))






/-! ## 4. Exact moments of the isolated-vertex count -/





/-! ## 5. The quantitative bound and the threshold -/







/-! ## 6. The classical regime `p = c·log n / n` with `0 < c < 1` -/




/-! ## 7. Above the threshold: the isolated-vertex obstruction disappears

The matching *first-moment* half.  For `p = c·log n/n` with `c > 1` the expected number
of isolated vertices tends to `0`, so a.a.s. `G(n,p)` has **no** isolated vertex — the
unique obstruction to connectivity at this density. -/





/-! ## 8. The sharp threshold for isolated vertices at `log n / n` -/






end ErdosRenyi


