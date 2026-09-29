-- Prove2me | Definitions.Def_Novelty_VertexRamseyThreshold
-- name    : Novelty_VertexRamseyThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:50:17.60363+00:00
-- url     : https://prove2.me/theorems/f9bfb06b-6c1a-411b-b650-bc96d956fb0a
-- title:
--   Aether Catalog definitions — Novelty_VertexRamseyThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.VertexRamseyThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/VertexRamseyThreshold.lean by skeleton subtraction
import Mathlib
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

namespace VertexRamsey

variable {V : Type*} {κ : Type*}

/-- `VertexArrows G s` is the vertex-Ramsey property `G →_v (K_{s i})_i`: every
`κ`-colouring `c` of the vertices of `G` admits a colour `i` and a `G`-clique
`S` of exactly `s i` vertices, all coloured `i`. -/
def VertexArrows (G : SimpleGraph V) (s : κ → ℕ) : Prop :=
  ∀ c : V → κ, ∃ (i : κ) (S : Finset V),
    (∀ v ∈ S, c v = i) ∧ S.card = s i ∧ G.IsClique (S : Set V)










/-! ## General target graphs (beyond cliques)

We now allow arbitrary target graphs `H i` on finite vertex types `β i` instead
of cliques `K_{s i}`.  A *monochromatic copy* of `H i` is an injection
`f : β i → V` that preserves adjacency (`H i`-edges map to `G`-edges) with
monochromatic image.  On the complete host, a monochromatic clique of size
`|β i|` already contains such a copy, so the exact clique threshold transfers:
`Kₙ` vertex-arrows the family `(H i)` as soon as `∑ i, (|β i| − 1) < n`. -/

/-- `GraphVertexArrows G H`: every colouring of the vertices of `G` yields a
colour `i` and a monochromatic copy of `H i` in `G` — an injective
adjacency-preserving map `f : β i → V` with `c (f w) = i` for all `w`. -/
def GraphVertexArrows {β : κ → Type*} (G : SimpleGraph V)
    (H : ∀ i, SimpleGraph (β i)) : Prop :=
  ∀ c : V → κ, ∃ (i : κ) (f : β i → V), Function.Injective f ∧
    (∀ w w', (H i).Adj w w' → G.Adj (f w) (f w')) ∧ (∀ w, c (f w) = i)

/-
**General target graphs on the complete host.** If
`∑ i, (Fintype.card (β i) − 1) < n` then `Kₙ` vertex-arrows the family of
arbitrary target graphs `(H i)`: every colouring contains a monochromatic copy
of some `H i`.  This reduces the general vertex-Ramsey property to the clique
threshold `completeGraph_vertexArrows`.
-/

/-! ## The `r`-colour "monochromatic edge" specialisation

Taking every target to be `K₂` (a single edge) recovers the classical
pigeonhole: `Kₙ` with `r` colours has two equally-coloured adjacent vertices iff
`n > r`. -/





end VertexRamsey


