-- Prove2me | Definitions.Def_Bridges_GenTuranAsymptoticBridge
-- name    : Bridges_GenTuranAsymptoticBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:14.458058+00:00
-- url     : https://prove2.me/theorems/43d8c54e-c0c7-4b82-a620-4152b8639162
-- title:
--   Aether Catalog definitions — Bridges_GenTuranAsymptoticBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GenTuranAsymptoticBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GenTuranAsymptoticBridge.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge: Generalized Turán counting (extremal combinatorics) ↔ Landau asymptotics (analysis)

The generalized Turán problem asks for the maximum number of copies of a fixed graph `H`
inside an `n`-vertex host graph that avoids a forbidden subgraph `F`.  For `H = K_{a,b}` and
`F = K_{3,b+1}` (with `3 ≤ a ≤ b`) the maximum is `Θ(n^3)`; the *upper* half of this statement
is a Kővári–Sós–Turán-style double count, reproduced here self-containedly as
`KabCopies_cubic_of_K3tFree`.

This file is a **connector**: it re-expresses that purely combinatorial cardinality bound as a
statement in the language of *asymptotic analysis*, using Mathlib's `Asymptotics.IsBigO` and
`Filter.Tendsto`.  Concretely, for any sequence `G : ∀ n, SimpleGraph (Fin n)` of
`K_{3,b+1}`-free graphs:

* `genTuran_KabCopies_isBigO` : the count `n ↦ #{copies of K_{a,b} in Gₙ}` is `O(n^3)` in the
  Landau sense (`=O[atTop]`).  The Landau constant is the *combinatorial* constant
  `C(b, a-3)` — the bridge carries the extremal constant into the analytic statement.
* `genTuran_density_tendsto_zero` : the normalized "copy density" `#copies / n^{a+b}` tends to
  `0`.  Since a labelled `K_{a,b}` lives on `a+b ≥ 6` vertices while the count is only cubic,
  the fraction of vertex placements realizing a copy vanishes — a probabilistic/analytic
  reading of the same extremal fact.

The two named results genuinely *consume* the combinatorial theorem `KabCopies_cubic_of_K3tFree`
as a black box, so the file is a faithful bridge rather than a restatement.

## Catalog connections
* `Generalized Turán number` / `Alon–Shikhelman`: `KabCopies` is the counting object.
* `Kővári–Sós–Turán theorem`: `cnbhd_card_le` is the common-neighborhood cap that drives the
  double count.
* `Complete bipartite graphs`: both the counted graph `K_{a,b}` and the forbidden `K_{3,b+1}`.
-/

open Finset

namespace GenTuranK3t

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The combinatorial core (self-contained upper bound)

The material in this section reproduces the elementary `O(n^3)` upper bound for
`ex(n, K_{a,b}, K_{3,t})`, so that the asymptotic bridge below is self-contained. -/

/-- Common neighborhood of a finite set `S` of vertices: all vertices adjacent to every vertex
of `S`. -/
def cnbhd (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  univ.filter (fun w => ∀ u ∈ S, G.Adj u w)



/-- The set of labelled copies of `K_{a,b}` in `G`: pairs `(A, B)` of disjoint vertex sets of
sizes `a` and `b` with every `A`–`B` edge present. -/
def KabCopies (G : SimpleGraph V) [DecidableRel G.Adj] (a b : ℕ) : Finset (Finset V × Finset V) :=
  (univ.powersetCard a ×ˢ univ.powersetCard b).filter
    (fun p => Disjoint p.1 p.2 ∧ ∀ u ∈ p.1, ∀ v ∈ p.2, G.Adj u v)


/-- `K_{3,t}`-freeness, stated via the actual bipartite subgraph: there is no pair of disjoint
vertex sets of sizes `3` and `t` with all cross edges present. -/
def K3tFree (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : Prop :=
  ¬ ∃ A B : Finset V, A.card = 3 ∧ B.card = t ∧ Disjoint A B ∧ ∀ u ∈ A, ∀ v ∈ B, G.Adj u v

/-- The common-neighborhood reformulation: every triple has at most `t-1` common neighbors. -/
def CNbound (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : Prop :=
  ∀ S : Finset V, S.card = 3 → (cnbhd G S).card ≤ t - 1








/-! ## The bridge to asymptotic analysis

We now carry the combinatorial cubic bound into the language of Landau `O`-notation and limits,
for arbitrary sequences of `K_{3,b+1}`-free graphs. -/

open Filter Asymptotics



end GenTuranK3t


