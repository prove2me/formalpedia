-- Prove2me | Definitions.Def_Novelty_Binary
-- name    : Novelty_Binary
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:07:39.345535+00:00
-- url     : https://prove2.me/theorems/4d9da194-3b4f-4689-925c-bc176258521d
-- title:
--   Aether Catalog definitions — Novelty_Binary
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Binary`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Binary.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_General
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cycle-containing families over a binary alphabet (`b = 2`)

For the binary alphabet `Fin 2` the bipartite graph of a pair has only four
possible edges, and its **only** possible cycle is the 4-cycle of the complete
bipartite graph `K₂,₂`.  Hence a pair `(u, v)` is cycle-containing iff all four
"patterns" `(s, t) ∈ Fin 2 × Fin 2` occur among the coordinates — the classical
notion of two binary vectors being *qualitatively independent*.

We package this combinatorial criterion as `Shatter`, connect it to the genuine
graph-theoretic predicate `ContainsCycle` from `CycleFamilies.General` via
`shatter_containsCycle`, and use it to:

* `shatter_k_ge_four`      : a shattering pair forces `4 ≤ k` (sharp threshold);
* `shatter_snoc`           : shattering is preserved by extending vectors, so the
                              extremal function is monotone in `k`;
* `exists_cyclicFamily_card_three` : an explicit **genuinely cycle-containing**
                              family of three vectors at `k = 4`, matching the
                              exhaustively-computed maximum (see
                              `ComputationalEvidence.md`).

-- !-- Lab Notes -- !--
Hypothesis  : Over `Fin 2` the graph cycle condition is equivalent to "all four
              patterns appear" (qualitative independence), and the maximum cyclic
              family has sizes `1,1,3,4,10,15,…` for `k = 2,3,4,5,6,7`.
Experiment  : Brute-force max-clique enumeration produced the sequence above.
              Formally, `Shatter` says the coordinate map `i ↦ (u i, v i)` is onto
              `Fin 2 × Fin 2`; surjectivity onto a 4-element type forces `k ≥ 4`.
              The explicit triple `{0011, 0101, 0110}` was verified to be pairwise
              shattering by `decide`, then promoted to genuine `ContainsCycle` via
              the constructed 4-cycle walk `shatter_containsCycle`.
Analysis    : Lower bound `3` at `k = 4` is exact (brute force gives `3`); proving
              the matching *upper* bound `≤ 3` for `k = 4`, and the general formula
              `N₂(k)`, are open (recorded in FUTURE_DIRECTIONS).  The threshold and
              monotonicity are the clean, fully-formal facts.
Critique    : `decide` is used only for the finite verification of a *single*
              witness family, never as the proof of a structural theorem.  The
              structural theorems use `Fintype.card_le_of_surjective`, an explicit
              walk construction, and `Fin.snoc` case analysis.
Synthesis   : The binary world realises the general girth bound sharply and
              exhibits the first nontrivial cyclic families.
-/

open SimpleGraph Finset

namespace Catalog.Novelty.CycleFamilies

variable {k : ℕ}

/-- Two binary vectors *shatter* if all four patterns `(s, t)` occur among the
coordinates.  For `b = 2` this is exactly the condition that the bipartite graph
contains a cycle (its unique cycle is the `K₂,₂` 4-cycle). -/
def Shatter (u v : Fin k → Fin 2) : Prop := ∀ s t : Fin 2, ∃ i, u i = s ∧ v i = t





/-- An explicit pairwise-shattering triple of length-4 binary vectors. -/
def w1 : Fin 4 → Fin 2 := ![0, 0, 1, 1]
def w2 : Fin 4 → Fin 2 := ![0, 1, 0, 1]
def w3 : Fin 4 → Fin 2 := ![0, 1, 1, 0]



end Catalog.Novelty.CycleFamilies


