-- Prove2me | Theorems.Thm_VertexRamsey_exists_bounded_coloring
-- name    : VertexRamsey.exists_bounded_coloring
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:40:35.844844+00:00
-- url     : https://prove2.me/theorems/382926d7-bbcc-4c64-88eb-1cfde4667b6b
-- title:
--   Capacity-respecting colouring.
-- statement:
--   **Capacity-respecting colouring.** If the total capacity `∑ i, cap i` is at
--   least `|V|`, there is a colouring with every colour class `i` of size at most
--   `cap i`.  Proved by embedding `V` into the disjoint union `Σ i, Fin (cap i)` and
--   reading off the first coordinate.
--
--   ```lean
--   theorem VertexRamsey.exists_bounded_coloring[Fintype V] [Fintype κ] [DecidableEq κ]
--       {cap : κ → ℕ} (h : Fintype.card V ≤ ∑ i, cap i) :
--       ∃ c : V → κ, ∀ i, (univ.filter (fun v => c v = i)).card ≤ cap i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/VertexRamseyThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/VertexRamseyThreshold.lean#L116

-- Thm stub generated from Novelty/VertexRamseyThreshold.lean
import Mathlib
import Definitions.Def_Novelty_VertexRamseyThreshold
/-
# The exact vertex-Ramsey threshold for complete host graphs

This file develops the deterministic combinatorial core underlying the
*vertex-Ramsey property* studied in the random-perturbation model of
Łuczak–Ruciński–Voigt (1993), Kreuter (1996) and Das–Morris–Treglown (2020).

Given a finite palette of colours `κ` and target clique sizes `s : κ → ℕ`, we
say a graph `G` **vertex-arrows** `s`, written `G →_v (K_{s i})_{i}`, if every
`κ`-colouring of `V(G)` produces some colour `i` together with a `G`-clique on
`s i` vertices, all coloured `i`.  (Taking `s i = ω(H i)` recovers the
clique-based reduction of the general `(H₁,…,H_r)_v`-Ramsey property, since a
monochromatic `H i` forces a monochromatic clique of size `ω(H i)` and, for the
complete host, conversely.)

## Main results

* `VertexRamsey.vertexArrows_of_isClique` — a purely combinatorial sufficient
  condition: if `G` contains a clique on more than `∑ i, (s i - 1)` vertices
  then `G →_v (K_{s i})_i`.
* `VertexRamsey.completeGraph_vertexArrows` /
  `VertexRamsey.completeGraph_not_vertexArrows` — the two directions of the
  **exact threshold** on the complete graph `Kₙ`.
* `VertexRamsey.completeGraph_vertexArrows_iff` — the sharp characterisation
  `Kₙ →_v (K_{s i})_i  ↔  ∑ i, (s i - 1) < n` (for `s i ≥ 1`).  Equivalently the
  vertex-Ramsey number of the clique family is `1 + ∑ i (s i - 1)`.
* `VertexRamsey.VertexArrows.mono_graph`, `VertexRamsey.VertexArrows.mono_size`
  — monotonicity in the host graph and in the target sizes.
* `VertexRamsey.exists_bounded_coloring` — the extremal colouring used for the
  lower bound (a capacity-respecting colouring exists whenever the total
  capacity is large enough), proved via an embedding into a sigma type.
* `VertexRamsey.edge_ramsey_iff` and the concrete instances afterwards — the
  `r`-colour "monochromatic edge" specialisation `s ≡ 2`, whose threshold
  `Kₙ →_v (K₂,…,K₂)  ↔  r < n` is the classical pigeonhole statement.

## A remark on the conjectured density threshold

The random-perturbation conjecture is phrased with the *product*
`ψ = ∏_j (ω(H j) - 1)` and density `1 - 1/ψ` (a Turán / edge-density parameter).
The results here isolate the *vertex* side, where the governing quantity is the
**sum** `∑_j (ω(H j) - 1)`: the vertex-Ramsey number of a clique family is
`1 + ∑_j (ω(H j) - 1)`.  This sum-versus-product distinction is recorded in
`FUTURE_DIRECTIONS.md`.
-/

open Finset

open VertexRamsey

variable {V : Type*} {κ : Type*}

theorem VertexRamsey.exists_bounded_coloring[Fintype V] [Fintype κ] [DecidableEq κ]
    {cap : κ → ℕ} (h : Fintype.card V ≤ ∑ i, cap i) :
    ∃ c : V → κ, ∀ i, (univ.filter (fun v => c v = i)).card ≤ cap i := by sorry
