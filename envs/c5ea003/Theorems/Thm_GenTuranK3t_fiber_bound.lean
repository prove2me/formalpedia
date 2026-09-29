-- Prove2me | Theorems.Thm_GenTuranK3t_fiber_bound
-- name    : GenTuranK3t.fiber_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:58:07.863033+00:00
-- url     : https://prove2.me/theorems/83971f77-f0d4-4528-aa00-cd5499786863
-- title:
--   Core fiber bound.
-- statement:
--   **Core fiber bound.** For a fixed triple `S`, the copies of `K_{a,b}` whose `a`-side
--   contains `S` are at most `C(t-1, b) · C(t-1, a-3)` in number.  The proof injects such a copy
--   `(A, B)` to the pair `(A \ S, B)`, where `B` ranges over the (size `≤ t-1`) common
--   neighborhood of `S` and `A \ S` over the (size `≤ t-1`) common neighborhood of `B`.
--
--   ```lean
--   theorem GenTuranK3t.fiber_bound(G : SimpleGraph V) [DecidableRel G.Adj] {a b t : ℕ} (hcn : CNbound G t)
--       (hb : 3 ≤ b) {S : Finset V} (hS : S.card = 3) :
--       ((KabCopies G a b).filter (fun p => S ⊆ p.1)).card
--         ≤ (t - 1).choose b * (t - 1).choose (a - 3) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GenTuranK3tUpperBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GenTuranK3tUpperBound.lean#L128

-- Thm stub generated from Novelty/GenTuranK3tUpperBound.lean
import Mathlib
import Definitions.Def_Novelty_GenTuranK3tUpperBound
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

open GenTuranK3t

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GenTuranK3t.fiber_bound(G : SimpleGraph V) [DecidableRel G.Adj] {a b t : ℕ} (hcn : CNbound G t)
    (hb : 3 ≤ b) {S : Finset V} (hS : S.card = 3) :
    ((KabCopies G a b).filter (fun p => S ⊆ p.1)).card
      ≤ (t - 1).choose b * (t - 1).choose (a - 3) := by sorry
