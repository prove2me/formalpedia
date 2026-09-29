-- Prove2me | solution 1 for Catalog.Combinatorics.BipartiteExtremalTrees.card_edgeFinset_bipCirculant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:22:47.310553+00:00
-- url     : https://prove2.me/submissions/34f3a3fd-237b-41b8-aaae-561efe96e010

import Mathlib
import Definitions.Def_Combinatorics_BipartiteExtremalTrees
open Catalog.Combinatorics.BipartiteExtremalTrees Finset in
theorem solution {N k : ℕ} (h : k ≤ N) : #(bipCirculant N k).edgeFinset = k * N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- no vertices, no edges
    obtain rfl : k = 0 := by omega
    simp [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  -- `k` residues `d` with `d.val < k`
  have hcnt : (univ.filter fun d : Fin (n + 1) => d.val < k).card = k := by
    have hmap : (univ.filter fun d : Fin (n + 1) => d.val < k).map Fin.valEmbedding = range k := by
      ext x
      simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact hd
      · intro hx
        exact ⟨⟨x, by omega⟩, hx, rfl⟩
    rw [← card_map Fin.valEmbedding, hmap, card_range]
  -- neighbourhoods: a left vertex `i` sees the right vertices `j` with `j - i < k`, and dually
  have hnbL : ∀ i, (bipCirculant (n + 1) k).neighborFinset (Sum.inl i)
      = (univ.filter fun b : Fin (n + 1) => (b - i).val < k).map Function.Embedding.inr := by
    intro i
    ext w
    cases w <;> simp [SimpleGraph.mem_neighborFinset, bipCirculant]
  have hnbR : ∀ j, (bipCirculant (n + 1) k).neighborFinset (Sum.inr j)
      = (univ.filter fun a : Fin (n + 1) => (j - a).val < k).map Function.Embedding.inl := by
    intro j
    ext w
    cases w <;> simp [SimpleGraph.mem_neighborFinset, bipCirculant]
  have hdeg : ∀ v, (bipCirculant (n + 1) k).degree v = k := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    cases v with
    | inl i =>
      rw [hnbL, card_map]
      refine (card_nbij' (t := univ.filter fun d : Fin (n + 1) => d.val < k)
        (fun b => b - i) (fun d => d + i) (by intro b hb; simpa using hb)
        (by intro d hd; simpa using hd) (by intro b _; simp) (by intro d _; simp)).trans hcnt
    | inr j =>
      rw [hnbR, card_map]
      refine (card_nbij' (t := univ.filter fun d : Fin (n + 1) => d.val < k)
        (fun a => j - a) (fun d => j - d) (by intro a ha; simpa using ha)
        (by intro d hd; simpa using hd) (by intro a _; simp) (by intro d _; simp)).trans hcnt
  -- handshake: `Σ deg = 2 · #edges`
  have hsum := (bipCirculant (n + 1) k).sum_degrees_eq_twice_card_edges
  simp only [hdeg, sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, smul_eq_mul] at hsum
  linarith
