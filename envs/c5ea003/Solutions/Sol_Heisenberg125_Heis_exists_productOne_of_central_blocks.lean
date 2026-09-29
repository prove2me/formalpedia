-- Prove2me | solution 1 for Heisenberg125.Heis.exists_productOne_of_central_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:23:18.402784+00:00
-- url     : https://prove2.me/submissions/90ccbd63-2429-4015-8a6d-594e9fedb1d1

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_CosetBound

open Heisenberg125 Heis Finset in
theorem solution {p : ℕ} [NeZero p] {Bs : List (List (Heis p))}
    (hne : ∀ B ∈ Bs, B ≠ []) (hcen : ∀ B ∈ Bs, (B.prod).a = 0 ∧ (B.prod).b = 0)
    (hlen : p ≤ Bs.length) :
    ∃ T : List (Heis p), T.Sublist Bs.flatten ∧ T ≠ [] ∧ T.prod = 1 := by
  classical
  -- central block products multiply by adding their `c`-coordinates
  have hcentral : ∀ L : List (List (Heis p)), (∀ B ∈ L, (B.prod).a = 0 ∧ (B.prod).b = 0) →
      (L.map List.prod).prod = ⟨0, 0, (L.map (fun B => (B.prod).c)).sum⟩ := by
    intro L
    induction L with
    | nil =>
      intro _
      ext <;> simp
    | cons B L ih =>
      intro hL
      obtain ⟨ha, hb⟩ := hL B (List.mem_cons_self ..)
      rw [List.map_cons, List.prod_cons, ih (fun x hx => hL x (List.mem_cons_of_mem B hx))]
      ext <;> simp [ha, hb]
  -- a run of blocks with zero `c`-sum is a product-one subsequence
  have key : ∀ i j : ℕ, i < j → j ≤ Bs.length →
      ((Bs.take j).map (fun B => (B.prod).c)).sum
        = ((Bs.take i).map (fun B => (B.prod).c)).sum →
      ∃ T : List (Heis p), T.Sublist Bs.flatten ∧ T ≠ [] ∧ T.prod = 1 := by
    intro i j hij hj hsum
    set R := (Bs.drop i).take (j - i) with hR
    have hRsub : R.Sublist Bs := (List.take_sublist _ _).trans (List.drop_sublist _ _)
    refine ⟨R.flatten, hRsub.flatten, ?_, ?_⟩
    · intro hnil
      rw [List.flatten_eq_nil_iff] at hnil
      have hRlen : R.length = j - i := by
        rw [hR, List.length_take, List.length_drop]
        omega
      obtain ⟨B, hB⟩ : ∃ B, B ∈ R := List.exists_mem_of_length_pos (by omega)
      exact hne B (hRsub.subset hB) (hnil B hB)
    · rw [List.prod_flatten, hcentral R (fun B hB => hcen B (hRsub.subset hB))]
      have hsplit : Bs.take j = Bs.take i ++ R := by
        rw [hR, ← List.take_add]
        congr 1
        omega
      rw [hsplit, List.map_append, List.sum_append] at hsum
      have h0 : (R.map (fun B => (B.prod).c)).sum = 0 := by
        linear_combination hsum
      rw [h0]
      ext <;> simp
  -- pigeonhole on the `p + 1` prefix sums in `ZMod p`
  let f : Fin (p + 1) → ZMod p := fun i => ((Bs.take i).map (fun B => (B.prod).c)).sum
  obtain ⟨x, y, hxy, hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt f
    (by rw [ZMod.card, Fintype.card_fin]; omega)
  have hx := x.isLt
  have hy := y.isLt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with h | h
  · exact key x y h (by omega) hfxy.symm
  · exact key y x h (by omega) hfxy
