-- Prove2me | solution 1 for GenTuranK3t.KabCopies_card_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:45:09.656633+00:00
-- url     : https://prove2.me/submissions/777ddb67-1cf7-48d9-821a-b7d985788868

-- Sol generated from Novelty/GenTuranK3tUpperBound.lean
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





lemma mem_KabCopies (G : SimpleGraph V) [DecidableRel G.Adj] {a b : ℕ}
    {p : Finset V × Finset V} :
    p ∈ KabCopies G a b ↔
      p.1.card = a ∧ p.2.card = b ∧ Disjoint p.1 p.2 ∧ ∀ u ∈ p.1, ∀ v ∈ p.2, G.Adj u v := by
  simp only [KabCopies, mem_filter, mem_product, mem_powersetCard, subset_univ, true_and]
  tauto





/-- Filtering size-`n` subsets of `univ` by `⊆ T` recovers the size-`n` subsets of `T`. -/
lemma powersetCard_filter_subset (n : ℕ) (T : Finset V) :
    (univ.powersetCard n).filter (fun S => S ⊆ T) = T.powersetCard n := by
  ext S
  simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
  tauto






open GenTuranK3t in
theorem solution(G : SimpleGraph V) [DecidableRel G.Adj] {a b : ℕ} (ha : 3 ≤ a) :
    (KabCopies G a b).card
      ≤ ∑ S ∈ univ.powersetCard 3, ((KabCopies G a b).filter (fun p => S ⊆ p.1)).card := by
  calc (KabCopies G a b).card
      = ∑ _p ∈ KabCopies G a b, 1 := by rw [card_eq_sum_ones]
    _ ≤ ∑ p ∈ KabCopies G a b, p.1.card.choose 3 := by
          apply Finset.sum_le_sum; intro p hp
          rw [mem_KabCopies] at hp
          rw [hp.1]; exact Nat.choose_pos ha
    _ = ∑ p ∈ KabCopies G a b, ((univ.powersetCard 3).filter (· ⊆ p.1)).card := by
          apply Finset.sum_congr rfl; intro p _
          rw [powersetCard_filter_subset, card_powersetCard]
    _ = ∑ p ∈ KabCopies G a b, ∑ S ∈ univ.powersetCard 3, (if S ⊆ p.1 then 1 else 0) := by
          apply Finset.sum_congr rfl; intro p _; rw [Finset.card_filter]
    _ = ∑ S ∈ univ.powersetCard 3, ∑ p ∈ KabCopies G a b, (if S ⊆ p.1 then 1 else 0) :=
          Finset.sum_comm
    _ = ∑ S ∈ univ.powersetCard 3, ((KabCopies G a b).filter (fun p => S ⊆ p.1)).card := by
          apply Finset.sum_congr rfl; intro S _; rw [Finset.card_filter]
