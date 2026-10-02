-- Prove2me | solution 1 for ProofsInTheBook.Chapter37.chapter37
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:13:11.300155+00:00
-- url     : https://prove2.me/submissions/5cb5497c-c258-4f9b-88d8-ccf303c6ecbd

import Mathlib


/-!
# Chapter 37: Turán's graph theorem

From "Proofs from THE BOOK":

**Turán's theorem**: The maximum number of edges in a K_{r+1}-free
graph on n vertices is achieved uniquely by the Turán graph T(n,r),
the complete r-partite graph with parts as equal as possible.

The book presents two proofs:
1. Turán's original proof by induction on n.
2. Zykov's symmetrization argument: replacing a vertex with a copy
   of a non-adjacent vertex can only increase the edge count
   while preserving K_{r+1}-freeness.
-/

namespace ProofsInTheBook.Chapter37

open SimpleGraph

/-!
### Turán's theorem: the Turán graph is extremal

The Turán graph `T(n,r)` is the unique `K_{r+1}`-free graph on `Fin n`
vertices with the maximum number of edges, up to graph isomorphism.
-/

theorem chapter37_turan (n r : ℕ) (hr : 0 < r) :
    (turanGraph n r).IsTuranMaximal r :=
  isTuranMaximal_turanGraph hr

private def turanGraph_congr {m n r : ℕ} (h : m = n) :
    turanGraph m r ≃g turanGraph n r :=
  { finCongr h with
    map_rel_iff' := by
      intro v w
      simp [turanGraph_adj] }

/-- Extremal-structure form of Turán's theorem.

A graph on `n` labeled vertices is Turán-maximal exactly when it is isomorphic
to the canonical Turán graph `turanGraph n r`. -/
theorem chapter37_extremal_structure (n r : ℕ) (hr : 0 < r) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph n r) := by
  intro G _
  constructor
  · intro hG
    rcases hG.nonempty_iso_turanGraph with ⟨e⟩
    exact ⟨(turanGraph_congr (Fintype.card_fin n)).comp e⟩
  · intro hG
    exact isTuranMaximal_of_iso hG.some hr

/-- Edge-count form of the uniqueness half.

If a `K_{r+1}`-free graph on `Fin n` has as many edges as `turanGraph n r`,
then it is isomorphic to the Turán graph. -/
theorem chapter37_unique_of_card_edgeFinset_eq (n r : ℕ) (hr : 0 < r)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : G.CliqueFree (r + 1))
    (hcard : Finset.card G.edgeFinset = Finset.card (turanGraph n r).edgeFinset) :
    Nonempty (G ≃g turanGraph n r) := by
  exact (chapter37_extremal_structure n r hr G).mp
    ⟨hfree, fun H _ hH => by
      have hle := (chapter37_turan n r hr).2 hH
      simpa [hcard] using hle⟩

/-- Edge-count characterization of all extremal `K_{r+1}`-free graphs on `Fin n`. -/
theorem chapter37_card_edgeFinset_eq_iff_nonempty_iso (n r : ℕ) (hr : 0 < r)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    G.CliqueFree (r + 1) ∧
        Finset.card G.edgeFinset = Finset.card (turanGraph n r).edgeFinset ↔
      Nonempty (G ≃g turanGraph n r) := by
  constructor
  · rintro ⟨hfree, hcard⟩
    exact chapter37_unique_of_card_edgeFinset_eq n r hr G hfree hcard
  · rintro ⟨e⟩
    exact ⟨(turanGraph_cliqueFree (n := n) hr).comap e.isContained,
      e.card_edgeFinset_eq⟩



end ProofsInTheBook.Chapter37

open SimpleGraph
open ProofsInTheBook.Chapter37

theorem solution (n r : ℕ) (hr : 0 < r) :
    (turanGraph n r).IsTuranMaximal r ∧
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.CliqueFree (r + 1) ∧
            Finset.card G.edgeFinset = Finset.card (turanGraph n r).edgeFinset ↔
          Nonempty (G ≃g turanGraph n r) := by
  exact ⟨chapter37_turan n r hr,
    fun G _ => chapter37_card_edgeFinset_eq_iff_nonempty_iso n r hr G⟩
