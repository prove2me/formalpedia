-- Prove2me | Theorems.Thm_EulerianParity_Trail_degree_eq_cast_add_succ
-- name    : EulerianParity.Trail.degree_eq_cast_add_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:10:51.431476+00:00
-- url     : https://prove2.me/theorems/75a665fa-7714-48bc-a83d-f6f18d22bec4
-- title:
--   Degree eq cast add succ
-- statement:
--   Formal statement of `EulerianParity.Trail.degree_eq_cast_add_succ` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem EulerianParity.Trail.degree_eq_cast_add_succ: degree G v = T.castCount v + T.succCount v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PosetTheory/EulerianParity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PosetTheory/EulerianParity.lean#L117

-- Thm stub generated from Geometry/PosetTheory/EulerianParity.lean
import Mathlib
import Definitions.Def_Geometry_PosetTheory_EulerianParity
/-
# Eulerian trails: the classical parity theorem

A small, self-contained development of the parity (handshake-style) theorem for
Eulerian trails in finite undirected multigraphs **with loops**.

## Model

* `Multigraph nV nE` is a finite multigraph on vertex set `Fin nV` with edge set
  `Fin nE`, given by two endpoint maps `endpt₁ endpt₂ : Fin nE → Fin nV`.
  A loop is an edge `e` with `endpt₁ e = endpt₂ e`.

* `degree G v` counts endpoint incidences at `v`, summing over **both** endpoint
  slots; hence a loop at `v` contributes `2`.

* `Trail G` is an Eulerian trail: a vertex walk `verts : Fin (nE+1) → Fin nV`
  together with a permutation `edgePerm` of the edges (so every edge is used
  exactly once) and a proof `adj` that the `i`-th step traverses edge
  `edgePerm i` between `verts i.castSucc` and `verts i.succ`, in either
  orientation.

## Main results

1. `Trail.parity_identity` — the local counting identity at every vertex `v`:
   `degree G v + startIndicator v + endIndicator v = 2 * visitCount v`.
   The proof is pure finite counting: each internal visit contributes two
   incidences, each endpoint one.

2. `Trail.odd_degree_isEndpoint` — if `Odd (degree G v)` then `v` is the start
   or the end vertex of the trail.

3. `Trail.card_oddDegree_le_two` — at most two vertices have odd degree.

4. `Trail.closed_even_degree` — if the trail is closed (start = end) then every
   vertex has even degree.
-/

open EulerianParity

open Finset


variable {nV nE : ℕ}



open Trail

variable {G : Multigraph nV nE}








variable (T : Trail G) (v : Fin nV)

/-
Splitting the walk at its last vertex.
-/

/-
Splitting the walk at its first vertex.
-/

/-
The degree of `v` equals the number of consecutive walk pairs incident to
`v` (first slot plus second slot). This is where the edge permutation and the
adjacency condition are used.
-/

theorem EulerianParity.Trail.degree_eq_cast_add_succ: degree G v = T.castCount v + T.succCount v := by sorry
