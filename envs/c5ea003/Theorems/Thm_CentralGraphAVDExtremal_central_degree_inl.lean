-- Prove2me | Theorems.Thm_CentralGraphAVDExtremal_central_degree_inl
-- name    : CentralGraphAVDExtremal.central_degree_inl
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:20:47.708132+00:00
-- url     : https://prove2.me/theorems/f5327c35-01dc-4c2b-98fc-2b39a5b95d1d
-- title:
--   Every original vertex of `C(G)` has degree `|V| − 1`.
-- statement:
--   Every original vertex of `C(G)` has degree `|V| − 1`.
--
--   ```lean
--   theorem CentralGraphAVDExtremal.central_degree_inl(v : V) :
--       (centralGraph G).degree (Sum.inl v) + 1 = Fintype.card V := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/CentralGraphAVDExtremal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/CentralGraphAVDExtremal.lean#L210

-- Thm stub generated from Novelty/CentralGraphAVDExtremal.lean
import Mathlib
import Definitions.Def_Novelty_CentralGraphAVDExtremal

/-!
# The extremal regime of AVD‑total colourings of central graphs of regular graphs

For a `d`‑regular graph `G` that is not complete, the **central graph** `C(G)`
(subdivide every edge, join every non‑adjacent pair) satisfies two lower bounds on
its adjacent‑vertex‑distinguishing (AVD) total chromatic number:

* a `d`‑governed bound  `χ''ₐ(C(G)) ≥ d + 3`, and
* a `|V|`‑governed bound `χ''ₐ(C(G)) ≥ |V(G)| + 1`   (every original vertex of
  `C(G)` has degree `|V(G)| − 1`).

Because a non‑complete `d`‑regular graph always has `|V(G)| ≥ d + 2`, the
`|V|`‑bound is **at least as strong** as the `d`‑bound, and the two coincide
*exactly* in the **extremal regime** `|V(G)| = d + 2`.

This file isolates and characterises that extremal regime, continuing the theory
developed for the central graph.  The main results are:

* `compl_isRegular` : the complement of a `d`‑regular graph on `n` vertices is
  `(n − 1 − d)`‑regular.
* `extremal_iff_compl_one_regular` : for a `d`‑regular non‑complete graph,
  `|V(G)| = d + 2` **iff** the complement is `1`‑regular (a perfect matching); i.e.
  the extremal graphs are precisely `K_{d+2}` minus a perfect matching (the
  cocktail‑party graphs).
* `dbound_le_cardbound` : `d + 3 ≤ |V(G)| + 1`, so the `|V|`‑bound dominates.
* `bounds_agree_iff_extremal` : the two bounds are **equal** iff `|V(G)| = d + 2`.
* `central_degree_inl_extremal` : in the extremal case every original vertex of
  `C(G)` has degree `d + 1`.
* `extremal_avd_ge` : in the extremal case every AVD total colouring of `C(G)` uses
  at least `|V(G)| + 1 = d + 3` colours — the two bounds collapse to a single sharp
  value.
* `cycleGraph_four_extremal` / `cycle4_avd_ge_four` : the `4`‑cycle `C₄` is the
  smallest extremal instance (`d = 2`, `|V| = 4`, complement `= 2K₂`), and its
  central graph needs at least `4` colours; while the `5`‑cycle is **not** extremal
  (`5 > 4`), witnessing the strictness of `dbound_le_cardbound`.

## Set‑up (recalled, self‑contained)

A *total colouring* of a finite simple graph `H` is modelled as a proper vertex
colouring of the **total graph** `T(H)` on `V(H) ⊕ E(H)`; it is **AVD** when
adjacent vertices receive distinct colour sets
`C(w) = {colour w} ∪ {colour e : e ∋ w}`.
-/

open SimpleGraph Finset

open CentralGraphAVDExtremal

/-! ## The total graph `T(H)` and total colourings -/


variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]





/-! ### The star clique -/





/-! ### Colour sets and AVD total colourings -/

variable {κ : Type*} [DecidableEq κ]






/-! ### Padding the palette preserves AVD -/



/-! ## The central graph `C(G)` -/


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem CentralGraphAVDExtremal.central_degree_inl(v : V) :
    (centralGraph G).degree (Sum.inl v) + 1 = Fintype.card V := by sorry
