-- Prove2me | Definitions.Def_Novelty_GenTuranK3tUpperBound
-- name    : Novelty_GenTuranK3tUpperBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:27:58.954168+00:00
-- url     : https://prove2.me/theorems/a9e8cec5-9ada-4165-8e8f-8b456f8b80e0
-- title:
--   Aether Catalog definitions — Novelty_GenTuranK3tUpperBound
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.GenTuranK3tUpperBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/GenTuranK3tUpperBound.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Necessary-threshold cubic upper bound for ex(n, K_{a,b}, K_{3,t})

This file formalizes the *upper* half of the generalized Turán statement
`ex(n, K_{a,b}, K_{3,t}) = Θ(n^3)`:

For every `K_{3,t}`-free graph `G` on a finite vertex set, the number of copies of the
complete bipartite graph `K_{a,b}` (with `3 ≤ a` and `3 ≤ b`) is at most
`C(n,3) · C(t-1, b) · C(t-1, a-3)`, hence `O(n^3)`.

The argument is a Kővári–Sós–Turán-style double count anchored on a 3-element "core":
every copy of `K_{a,b}` contains a copy of the `3`-side of `K_{3,t}` inside its `a`-side, and
`K_{3,t}`-freeness caps every triple's common neighborhood at `t-1`.  This is the elementary
direction that holds *uniformly at the conjectured necessary threshold* `t = b+1`, for every
parity of `b` (the parity subtlety in the literature lives entirely in the matching cubic
*lower-bound* construction).

## Catalog connections
* `Alon-Shikhelman generalized Turán numbers`: `KabCopies` is exactly the counting object whose
  maximum over `K_{3,t}`-free graphs is `ex(n, K_{a,b}, K_{3,t})`.
* `Kővári-Sós-Turán theorem`: `cnbhd_card_le` is the common-neighborhood cap that powers the
  classical KST counting argument, here lifted from edges to `K_{a,b}`-copies.
* `Janzer-Longbrake-Yepremyan theorem for ex(n,K_{a,b},K_{3,t})`: `KabCopies_cubic_of_K3tFree`
  is the `O(n^3)` upper bound matching their `Θ(n^3)` result.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): For `K_{3,t}`-free `G`, the number of `K_{a,b}` copies is `O(n^3)`,
  and crucially the *upper* bound needs only `t ≥ b+1` regardless of the parity of `b`.
Experiment (Experimenter): Formalized copies as disjoint complete-bipartite pairs `(A,B)`.
  Built a double count: anchor on a triple `S ⊆ A`; `K_{3,t}`-freeness gives `|N(S)| ≤ t-1`
  (so `B` lives in a set of size `≤ t-1`), and `|N(B)| ≤ t-1` (so `A \ S` lives in a set of
  size `≤ t-1`).  The map `(A,B) ↦ (A\S, B)` is injective on the `S`-fiber.
Analysis (Analyst): The "3" in `n^3` is forced — it is exactly the `3` of `K_{3,t}` — while the
  remaining `a+b-3` vertices are each pinned into a bounded common neighborhood.  The hypotheses
  `3 ≤ a` (to extract a triple from `A`) and `3 ≤ b` (to cap `N(B)`) are the genuine load.
Critique (Critic): `t ≥ b+1` is *not* used by the bound itself (`C(t-1,b)` simply vanishes when
  `b > t-1`); it is the threshold at which the matching lower bound becomes possible, so we keep
  it only in the headline `KabCopies_cubic_of_K3tFree`.  No theorem is vacuous: the count is a
  genuine `Finset.card`, and `K3tFree_iff_CNbound` ties the abstract cap to the honest
  subgraph-freeness definition.
Synthesis (PI): A clean, parity-uniform `O(n^3)` upper bound at the necessary threshold.
-/

open Finset

namespace GenTuranK3t

variable {V : Type*} [Fintype V] [DecidableEq V]

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








end GenTuranK3t


