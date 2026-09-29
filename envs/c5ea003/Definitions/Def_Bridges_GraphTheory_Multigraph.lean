-- Prove2me | Definitions.Def_Bridges_GraphTheory_Multigraph
-- name    : Bridges_GraphTheory_Multigraph
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:06.04808+00:00
-- url     : https://prove2.me/theorems/0a04d972-347c-4878-8de9-d431f5b2a2b4
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_Multigraph
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.Multigraph`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/Multigraph.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Finite Multigraphs

We define finite multigraphs with vertex set `Fin nV` and edge set `Fin nE`,
together with the notion of degree and the **Handshaking Lemma**.

## Main Definitions

* `Multigraph nV nE` : A multigraph with `nV` vertices and `nE` edges.
* `Multigraph.degree` : The degree of a vertex (counting each edge-endpoint incidence).

## Main Results

* `Multigraph.handshaking` : The sum of all vertex degrees equals `2 * nE`.
* `Multigraph.even_sum_degrees` : The sum of all vertex degrees is even.
-/

namespace Bridges

/-- A finite multigraph with vertex set `Fin nV` and edge set `Fin nE`.
Each edge has two endpoints (not necessarily distinct, allowing loops). -/
structure Multigraph (nV nE : ℕ) where
  /-- The first endpoint of each edge -/
  endpt₁ : Fin nE → Fin nV
  /-- The second endpoint of each edge -/
  endpt₂ : Fin nE → Fin nV

namespace Multigraph

variable {nV nE : ℕ} (G : Multigraph nV nE)

/-- The degree of a vertex `v`, defined as the total number of edge-endpoint
incidences at `v`. Each non-loop edge incident to `v` contributes 1; each
loop at `v` contributes 2. This is the standard multigraph degree. -/
def degree (v : Fin nV) : ℕ :=
  (Finset.univ.filter (fun e => G.endpt₁ e = v)).card +
  (Finset.univ.filter (fun e => G.endpt₂ e = v)).card

/-
**Handshaking Lemma**: The sum of all vertex degrees equals twice the number of edges.

This is one of the most fundamental results in graph theory. Each edge contributes
exactly 2 to the total degree sum (one for each endpoint).
-/

/-
The sum of all vertex degrees is even. An immediate corollary of the Handshaking Lemma.
-/

end Multigraph
end Bridges


