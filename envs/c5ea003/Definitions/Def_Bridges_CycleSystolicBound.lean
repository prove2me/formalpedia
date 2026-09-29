-- Prove2me | Definitions.Def_Bridges_CycleSystolicBound
-- name    : Bridges_CycleSystolicBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:25:52.474967+00:00
-- url     : https://prove2.me/theorems/d170bcee-d168-457e-9d5b-5852dea53acf
-- title:
--   Aether Catalog definitions — Bridges_CycleSystolicBound
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CycleSystolicBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CycleSystolicBound.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cycle-Systolic Lower Bounds for Communication Protocols

This file formalizes the **rectangle bound as a cycle-obstruction theorem**
for communication protocols on bipartite state graphs.

## Main Idea

A bounded-message protocol over a bipartite communication graph induces
a partition of the transcript into blocks. By pigeonhole, each block of
size exceeding the message alphabet must contain a repeated message.
Repeated messages produce alternating cycles in the bipartite state graph.
If every alternating cycle has cost at least `g` (the "cycle systole"),
then total protocol cost is at least `g * ⌊R/n⌋`.

This is a **discrete systolic inequality** for protocol dynamics.

## Main Results

* `protocol_cost_ge_cycleCost_mul_div` — The core additive block lower bound:
  if R rounds use n messages, and each block of n rounds has cost ≥ g,
  then total cost ≥ g * (R / n).

* `exists_repetition_in_block` — Pigeonhole on finite message alphabets:
  any function from `Fin (n+1)` to `Fin n` has a collision.

* `protocol_cost_ge_minCycle_mul_div` — The graph-theoretic communication
  lower bound: minimum alternating cycle cost controls total protocol cost.

* `rectangle_bound` — The full rectangle/cycle-obstruction theorem
  combining protocol structure with cycle cost lower bounds.

## Cross-Domain Connections

- **Automata minimization**: Message classes act as quotient states;
  repetition forces recurrence in the quotient automaton.
- **Tropical algebra**: Minimum cycle cost is a tropical invariant;
  the lower bound is a tropical energy accumulation law.
- **Transfer operators**: Protocol transcripts are control sequences;
  positive cycle systole prevents free recurrence.

-/


set_option maxHeartbeats 400000

open Finset BigOperators

namespace CycleSystolic

/-! ## Section 1: Alternating Cycles in Bipartite Graphs -/

/-- An alternating cycle in a bipartite graph with row vertices `Fin a`
and column vertices `Fin b`. The cycle visits `len` row-column pairs
in sequence. This models the fundamental geometric obstruction in
communication protocols: when messages repeat, state transitions
form closed alternating paths. -/
structure AltCycle (a b : ℕ) where
  len : ℕ
  len_pos : 0 < len
  row : Fin len → Fin a
  col : Fin len → Fin b

/-- The total cost of an alternating cycle under a weight matrix `W`.
Each edge `(row t, col t)` contributes `W (row t) (col t)` to the cost.
In the tropical/min-plus interpretation, this is the cycle weight
whose minimum over all cycles gives the tropical eigenvalue. -/
def AltCycle.cost {a b : ℕ} (W : Matrix (Fin a) (Fin b) ℕ) (C : AltCycle a b) : ℕ :=
  ∑ t : Fin C.len, W (C.row t) (C.col t)

/-- A value `g` is a minimum cycle cost for weight matrix `W` if every
alternating cycle has cost at least `g`. This is the **cycle systole**
of the bipartite communication graph — the fundamental geometric
invariant controlling protocol lower bounds.

In tropical algebra, this corresponds to the minimum tropical cycle
weight, which governs the asymptotic behavior of min-plus matrix powers. -/
def IsMinCycleCost {a b : ℕ} (W : Matrix (Fin a) (Fin b) ℕ) (g : ℕ) : Prop :=
  ∀ C : AltCycle a b, g ≤ C.cost W

/-! ## Section 2: Protocol Model -/

/-- A communication protocol over a bipartite state graph.
- `a` Alice states, `b` Bob states, `n` message symbols, `R` rounds.
- `msg t` is the message sent at round `t`.
- `alice t` / `bob t` are Alice's/Bob's states at round `t`.
- `roundCost t` is the cost contribution of round `t`.

This abstracts the essential structure: a finite-alphabet interaction
sequence over a bipartite state space, with an associated cost function. -/
structure Protocol (a b n R : ℕ) where
  msg : Fin R → Fin n
  alice : Fin R → Fin a
  bob : Fin R → Fin b
  roundCost : Fin R → ℕ

/-- Total cost of a protocol is the sum of per-round costs. -/
def Protocol.totalCost {a b n R : ℕ} (P : Protocol a b n R) : ℕ :=
  ∑ t : Fin R, P.roundCost t


/-! ## Section 3: The Core Additive Block Lower Bound -/

/-
**Core block lower bound theorem.**

If a protocol of `R` rounds can be decomposed into `R / n` disjoint blocks,
each with cost at least `g`, and the sum of block costs is bounded by
total protocol cost, then total cost is at least `g * (R / n)`.

This is the algebraic engine behind all cycle-systolic communication bounds.
The proof combines:
- `Finset.sum_le_sum` to replace each block cost by `g`
- the identity `∑ k : Fin m, g = g * m`
- transitivity with the block-to-total cost inequality
-/

/-! ## Section 4: Pigeonhole — Repetition in Finite-Alphabet Blocks -/

/-
**Pigeonhole repetition lemma.**

Any function from `Fin (n + 1)` to `Fin n` must have a collision.
This is the combinatorial engine that forces message repetition in
protocol blocks: with `n` possible messages, any block of `n + 1`
rounds must reuse at least one message.

In the automata interpretation, this is why bounded-alphabet protocols
cannot avoid revisiting equivalence classes of the quotient automaton.
-/

/-! ## Section 5: Block Start Utility -/

/-- Starting round index for the `k`-th consecutive block of size `n`. -/
def blockStart (R n : ℕ) (k : Fin (R / n)) : ℕ := k.1 * n

/-
Each block start is within bounds when `k < R / n`.
-/

/-! ## Section 6: Graph-Theoretic Communication Lower Bound -/

/-
**Communication cycle-cost lower bound.**

Given a weight matrix `W` with minimum alternating cycle cost `g`,
and a protocol that produces an alternating cycle in each of its
`R / n` blocks, with the sum of cycle costs bounded by total protocol
cost, the total cost is at least `g * (R / n)`.

This theorem connects three domains:
1. **Communication complexity**: bounded message alphabets force recurrence
2. **Graph theory**: recurrence produces alternating cycles with cost ≥ g
3. **Tropical algebra**: cycle costs are tropical eigenvalue witnesses
-/

/-! ## Section 7: The Rectangle Bound as Cycle Obstruction -/

/-
**The rectangle bound (cycle-obstruction form).**

For any protocol with `R` rounds over `n` messages on a bipartite graph
with minimum alternating cycle cost `g > 0`:
if each block of `n` consecutive rounds produces an alternating cycle
whose cost is accounted for by the protocol's round costs, then

  `g * (R / n) ≤ P.totalCost`

This is the **discrete systolic inequality** for communication protocols.
It says that positive cycle systole forces linear cost accumulation,
with rate controlled by the ratio of transcript length to alphabet size.

The theorem reinterprets the classical rectangle lower bound as a
*geometric obstruction*: rectangles in the communication matrix
correspond to alternating cycles in the state graph, and the minimum
cycle cost (systole) provides an inescapable per-block cost floor.
-/

/-! ## Section 8: Monotonicity and Strengthening Lemmas -/

/-
Cycle cost is monotone in the weight matrix: larger weights give larger cycle costs.
-/

/-
If `g` is a minimum cycle cost, then any `g' ≤ g` is also a minimum cycle cost.
-/

/-
More rounds or fewer messages give a stronger lower bound.
-/

/-! ## Section 9: Tropical Interpretation -/

/-
**Tropical cycle weight interpretation.**

In the min-plus (tropical) semiring, the relevant quantity is the
minimum total weight of any alternating cycle. This theorem states
that if the tropical cycle weight is at least `g`, then any protocol
with `R / n` forced cycles pays at least `g * (R / n)` in total.

This connects communication lower bounds to tropical spectral theory:
the minimum cycle weight is related to the tropical eigenvalue of
the associated min-plus matrix power.
-/

/-! ## Section 10: Edge-Disjoint Cycle Extraction -/

/-- The edge set of an alternating cycle: the set of (row, col) pairs visited. -/
def AltCycle.edgeSet {a b : ℕ} (C : AltCycle a b) : Finset (Fin a × Fin b) :=
  Finset.univ.image (fun t => (C.row t, C.col t))

/-
**Edge-disjoint cycle extraction theorem.**

If `R / n` pairwise edge-disjoint alternating cycles exist in the bipartite
graph, and each has cost at least `g`, then the total edge weight is at
least `g * (R / n)`.

This is the strongest form of the rectangle bound: it shows that
repeated messages in a protocol force not just cycles, but *edge-disjoint*
cycles, each consuming its own share of the communication cost.
-/

end CycleSystolic


