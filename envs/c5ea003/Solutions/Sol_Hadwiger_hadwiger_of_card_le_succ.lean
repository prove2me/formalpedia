-- Prove2me | solution 1 for Hadwiger.hadwiger_of_card_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:53:11.839978+00:00
-- url     : https://prove2.me/submissions/ba7c327d-a048-4f29-8c72-fa7377804d47

import Mathlib
import Definitions.Def_Probability_HadwigerK3
import Theorems.Thm_Hadwiger_completeMinor_of_isNClique
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QuickSmallGraphs
open Hadwiger SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- If `|V| ≤ k` then every graph on `V` is `k`-colourable. -/
theorem colorable_of_card_le [Fintype V] {k : ℕ} (hcard : Fintype.card V ≤ k) :
    G.Colorable k := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := V) (β := Fin k) (by simpa using hcard)
  exact ⟨Coloring.mk f fun {x y} hxy hcon => (G.ne_of_adj hxy) (f.injective hcon)⟩

/-- A graph on `k+1` vertices that is not `k`-colourable is complete. -/
theorem eq_top_of_not_colorable_of_card_le [Fintype V] {k : ℕ}
    (hcard : Fintype.card V ≤ k + 1) (h : ¬ G.Colorable k) : G = ⊤ := by
  classical
  ext u v
  simp only [top_adj]
  refine ⟨fun hadj => G.ne_of_adj hadj, fun hne => ?_⟩
  by_contra hadj
  -- identify `v` with `u`; the remaining `k` vertices get distinct colours
  have hcardsub : Fintype.card {x : V // x ≠ v} ≤ k := by
    have h1 : Fintype.card {x : V // x ≠ v} = Fintype.card V - 1 := by
      simp [Fintype.card_subtype_compl]
    have h2 : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := {x : V // x ≠ v}) (β := Fin k)
    (by simpa using hcardsub)
  refine h ⟨Coloring.mk (fun x => if hx : x = v then e ⟨u, hne⟩ else e ⟨x, hx⟩) ?_⟩
  intro x y hxy hcon
  dsimp only at hcon
  by_cases hxv : x = v <;> by_cases hyv : y = v
  · exact (G.ne_of_adj hxy) (hxv.trans hyv.symm)
  · rw [dif_pos hxv, dif_neg hyv] at hcon
    have : u = y := congrArg Subtype.val (e.injective hcon)
    exact hadj (by rw [← this] at hxy; rw [hxv] at hxy; exact hxy.symm)
  · rw [dif_neg hxv, dif_pos hyv] at hcon
    have : x = u := congrArg Subtype.val (e.injective hcon)
    exact hadj (by rw [this] at hxy; rw [hyv] at hxy; exact hxy)
  · rw [dif_neg hxv, dif_neg hyv] at hcon
    exact (G.ne_of_adj hxy) (congrArg Subtype.val (e.injective hcon))

/-- **Hadwiger's conjecture holds for all graphs with at most `k+1` vertices**,
for every `k` — including the open cases `k ≥ 5`. -/
theorem hadwiger_of_card_le_succ [Fintype V] {k : ℕ} (hcard : Fintype.card V ≤ k + 1)
    (h : ¬ G.Colorable k) : CompleteMinor (k + 1) G := by
  classical
  have htop : G = ⊤ := eq_top_of_not_colorable_of_card_le hcard h
  have hcardeq : Fintype.card V = k + 1 := by
    rcases Nat.lt_or_ge (Fintype.card V) (k + 1) with hlt | hge
    · exact absurd (colorable_of_card_le (by omega)) h
    · omega
  have hclique : G.IsNClique (k + 1) Finset.univ := by
    refine ⟨?_, by simpa using hcardeq⟩
    intro x _ y _ hxy
    rw [htop]
    exact hxy
  exact completeMinor_of_isNClique hclique

end QuickSmallGraphs
open Hadwiger SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
theorem solution [Fintype V] {k : ℕ} (hcard : Fintype.card V ≤ k + 1)
    (h : ¬ G.Colorable k) : CompleteMinor (k + 1) G := by
  exact QuickSmallGraphs.hadwiger_of_card_le_succ hcard h
#print axioms solution
