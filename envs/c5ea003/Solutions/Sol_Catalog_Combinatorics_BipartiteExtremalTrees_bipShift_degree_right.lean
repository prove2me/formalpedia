-- Prove2me | solution 1 for Catalog.Combinatorics.BipartiteExtremalTrees.bipShift_degree_right
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T04:29:37.916367+00:00
-- url     : https://prove2.me/submissions/679f17b2-44f4-45f9-875f-7795a5703a39

import Mathlib
import Definitions.Def_Combinatorics_BipartiteExtremalTrees
open Catalog.Combinatorics.BipartiteExtremalTrees in
theorem solution {m n k : ℕ} (h : m ≤ n) (hk : k ≤ n) (j : Fin n) :
    (bipShift m n k h).degree (Sum.inr j) ≤ k := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := j.pos; omega⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  -- a neighbour `inl i` is recorded by the offset `(j - i).val < k`, injectively
  let g : Fin m ⊕ Fin (n' + 1) → ℕ := Sum.elim (fun i => (j - Fin.castLE h i).val) (fun _ => 0)
  calc ((bipShift m (n' + 1) k h).neighborFinset (Sum.inr j)).card
        ≤ (Finset.range k).card := by
        apply Finset.card_le_card_of_injOn g
        · intro x hx
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hx
          rw [Finset.mem_coe]
          rcases x with i | j'
          · exact Finset.mem_range.mpr hx
          · exact absurd hx (by simp [bipShift])
        · intro x hx y hy hxy
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hx hy
          rcases x with i | j'
          · rcases y with i' | j''
            · have hv : j - Fin.castLE h i = j - Fin.castLE h i' := Fin.ext hxy
              rw [sub_right_inj] at hv
              rw [Fin.castLE_injective h hv]
            · exact absurd hy (by simp [bipShift])
          · exact absurd hx (by simp [bipShift])
    _ = k := Finset.card_range k
