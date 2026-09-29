-- Prove2me | Definitions.Def_Tropical_RiemannRoch_Basic
-- name    : Tropical_RiemannRoch_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:30.607763+00:00
-- url     : https://prove2.me/theorems/ea66e502-ff79-4ac4-9243-1dc20d3f64f5
-- title:
--   Aether Catalog definitions — Tropical_RiemannRoch_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.RiemannRoch.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/RiemannRoch/Basic.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. Released under Apache 2.0 license.

# Chip-firing and Baker–Norine divisor theory on a finite graph

This file develops the combinatorial ("tropical") theory of divisors on a finite
graph, the foundation of the Baker–Norine Riemann–Roch theorem.

## Main definitions

* `FinGraph`        — a finite loopless graph given by an integer-valued symmetric
                      adjacency (edge multiplicity) function.
* `Divisor G`       — an element of `G.V → ℤ` (a chip configuration).
* `deg D`           — the total number of chips.
* `prin f`          — the principal divisor obtained by firing with the integer
                      "firing vector" `f` (the image of the graph Laplacian).
* `LinEquiv D D'`   — linear equivalence: `D' = D + prin f` for some `f`.
* `canonical G`     — the canonical divisor `K(v) = deg(v) - 2`.
* `genus G`         — the (first Betti number) genus `|E| - |V| + 1`.

## Main results

* `deg_prin`               — every principal divisor has degree `0`
                             (chip-firing preserves the number of chips).
* `LinEquiv.deg_eq`        — linearly equivalent divisors have equal degree.
* `linEquiv_equivalence`   — `LinEquiv` is an equivalence relation.
* `even_totalEdges`        — the total degree `∑ deg(v)` is even.
* `deg_canonical`          — `deg K = 2 * genus - 2`  (the Riemann–Roch numeric shape).

-- !-- Lab Notes -- !--
Hypothesis: chip-firing is degree preserving and the canonical divisor of any
finite graph has degree `2g-2`.  Experiment: formalize firing as the Laplacian
image `prin f w = ∑ v adj(v,w)(f w - f v)` and compute degrees.  Analysis: the
degree-invariance proof is a single `Finset.sum_comm` once symmetry of `adj` is
used; the canonical-degree proof needs evenness of `∑ deg(v)`, which itself is a
symmetry/`sum_comm` fact.  Critique: definitions must be loopless and symmetric or
`deg_prin` fails; we enforce both in `FinGraph`.
-/


open Finset BigOperators

namespace BakerNorine

/-- A finite loopless graph: `adj v w` is the number of edges between `v` and `w`. -/
structure FinGraph where
  V : Type
  [finV : Fintype V]
  [decV : DecidableEq V]
  adj : V → V → ℕ
  adj_symm : ∀ v w, adj v w = adj w v
  adj_loopless : ∀ v, adj v v = 0

attribute [instance] FinGraph.finV FinGraph.decV

variable (G : FinGraph)

/-- A divisor (chip configuration) on `G`. -/
abbrev Divisor : Type := G.V → ℤ

variable {G}

/-- The degree of a divisor: the total number of chips. -/
def deg (D : Divisor G) : ℤ := ∑ v, D v

/-- The (integer) vertex degree of `v`: the number of edges incident to `v`. -/
def vertexDeg (G : FinGraph) (v : G.V) : ℤ := ∑ w, (G.adj v w : ℤ)

/-- The principal divisor obtained from the firing vector `f`.  Firing vertex `v`
with multiplicity `f v` sends `adj(v,w)` chips to each neighbour `w`. -/
def prin (f : G.V → ℤ) : Divisor G := fun w => ∑ v, (G.adj v w : ℤ) * (f w - f v)

/-- Linear equivalence of divisors: `D'` is reachable from `D` by chip-firing. -/
def LinEquiv (D D' : Divisor G) : Prop := ∃ f : G.V → ℤ, D' = fun w => D w + prin f w


/-- The canonical divisor `K(v) = deg(v) - 2`. -/
def canonical (G : FinGraph) : Divisor G := fun v => vertexDeg G v - 2

/-- The total degree `∑_v deg(v) = 2|E|`. -/
def totalEdges (G : FinGraph) : ℤ := ∑ v, vertexDeg G v

/-- The genus (first Betti number) `g = |E| - |V| + 1`. -/
def genus (G : FinGraph) : ℤ := totalEdges G / 2 - (Fintype.card G.V : ℤ) + 1


/-
Chip-firing preserves the total number of chips: principal divisors have degree 0.
-/


/-
`prin` is additive in the firing vector.
-/







/-
The total degree of a graph is even (each edge is counted twice).
-/

/-
**Canonical degree (Riemann–Roch numeric shape).**
The canonical divisor has degree `2g - 2`.
-/

end BakerNorine


