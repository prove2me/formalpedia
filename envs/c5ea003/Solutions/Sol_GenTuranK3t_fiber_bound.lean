-- Prove2me | solution 1 for GenTuranK3t.fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:45:10.342129+00:00
-- url     : https://prove2.me/submissions/b8961556-90bf-4b34-9527-28cdaea5bd70

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


@[simp] lemma mem_cnbhd (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (w : V) :
    w ∈ cnbhd G S ↔ ∀ u ∈ S, G.Adj u w := by
  simp [cnbhd]

/-- The common neighborhood is antitone in the set: adding constraints removes neighbors. -/
lemma cnbhd_antitone (G : SimpleGraph V) [DecidableRel G.Adj] {S T : Finset V} (h : S ⊆ T) :
    cnbhd G T ⊆ cnbhd G S := by
  intro w hw
  simp only [mem_cnbhd] at *
  exact fun u hu => hw u (h hu)


lemma mem_KabCopies (G : SimpleGraph V) [DecidableRel G.Adj] {a b : ℕ}
    {p : Finset V × Finset V} :
    p ∈ KabCopies G a b ↔
      p.1.card = a ∧ p.2.card = b ∧ Disjoint p.1 p.2 ∧ ∀ u ∈ p.1, ∀ v ∈ p.2, G.Adj u v := by
  simp only [KabCopies, mem_filter, mem_product, mem_powersetCard, subset_univ, true_and]
  tauto




/-- A triple's common neighborhood, and more generally any set of size `≥ 3`, is capped at
`t-1` neighbors under the common-neighborhood bound. -/
lemma cnbhd_card_le (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℕ} (hcn : CNbound G t)
    {B : Finset V} (hB : 3 ≤ B.card) : (cnbhd G B).card ≤ t - 1 := by
  obtain ⟨S, hSB, hScard⟩ := Finset.exists_subset_card_eq hB
  calc (cnbhd G B).card ≤ (cnbhd G S).card := card_le_card (cnbhd_antitone G hSB)
    _ ≤ t - 1 := hcn S hScard







open GenTuranK3t in
theorem solution(G : SimpleGraph V) [DecidableRel G.Adj] {a b t : ℕ} (hcn : CNbound G t)
    (hb : 3 ≤ b) {S : Finset V} (hS : S.card = 3) :
    ((KabCopies G a b).filter (fun p => S ⊆ p.1)).card
      ≤ (t - 1).choose b * (t - 1).choose (a - 3) := by
  classical
  set D : Finset (Finset V × Finset V) :=
    (cnbhd G S).powersetCard b |>.biUnion
      (fun B => ((cnbhd G B).powersetCard (a - 3)).image (fun R => (R, B))) with hD
  have hmaps : Set.MapsTo (fun p : Finset V × Finset V => (p.1 \ S, p.2))
      ((KabCopies G a b).filter (fun p => S ⊆ p.1)) D := by
    intro p hp
    simp only [mem_coe, mem_filter, mem_KabCopies] at hp
    obtain ⟨⟨hp1, hp2, _hdisj, hcomp⟩, hSsub⟩ := hp
    show (p.1 \ S, p.2) ∈ D
    rw [hD]
    apply Finset.mem_biUnion.mpr
    refine ⟨p.2, ?_, ?_⟩
    · rw [mem_powersetCard]
      refine ⟨?_, hp2⟩
      intro v hv; rw [mem_cnbhd]; intro u hu; exact hcomp u (hSsub hu) v hv
    · apply Finset.mem_image.mpr
      refine ⟨p.1 \ S, ?_, rfl⟩
      rw [mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro w hw
        rw [mem_sdiff] at hw
        rw [mem_cnbhd]; intro v hv; exact (hcomp w hw.1 v hv).symm
      · rw [card_sdiff_of_subset hSsub, hp1, hS]
  have hinj : Set.InjOn (fun p : Finset V × Finset V => (p.1 \ S, p.2))
      ((KabCopies G a b).filter (fun p => S ⊆ p.1)) := by
    intro p hp q hq hpq
    simp only [mem_coe, mem_filter] at hp hq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨hpd, hpq2⟩ := hpq
    have hps : S ⊆ p.1 := hp.2
    have hqs : S ⊆ q.1 := hq.2
    have e1 : p.1 = q.1 := by
      rw [← Finset.sdiff_union_of_subset hps, ← Finset.sdiff_union_of_subset hqs, hpd]
    exact Prod.ext e1 hpq2
  calc ((KabCopies G a b).filter (fun p => S ⊆ p.1)).card
      ≤ D.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ ∑ B ∈ (cnbhd G S).powersetCard b,
          (((cnbhd G B).powersetCard (a - 3)).image (fun R => (R, B))).card := by
          rw [hD]; exact Finset.card_biUnion_le
    _ ≤ ∑ B ∈ (cnbhd G S).powersetCard b, ((cnbhd G B).powersetCard (a - 3)).card := by
          apply Finset.sum_le_sum; intro B _; exact Finset.card_image_le
    _ ≤ ∑ B ∈ (cnbhd G S).powersetCard b, (t - 1).choose (a - 3) := by
          apply Finset.sum_le_sum; intro B hB
          rw [mem_powersetCard] at hB
          rw [card_powersetCard]
          exact Nat.choose_le_choose _ (cnbhd_card_le G hcn (by rw [hB.2]; exact hb))
    _ = ((cnbhd G S).powersetCard b).card * (t - 1).choose (a - 3) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ = (cnbhd G S).card.choose b * (t - 1).choose (a - 3) := by rw [card_powersetCard]
    _ ≤ (t - 1).choose b * (t - 1).choose (a - 3) := by
          apply Nat.mul_le_mul_right
          exact Nat.choose_le_choose _ (cnbhd_card_le G hcn (by rw [hS]))
