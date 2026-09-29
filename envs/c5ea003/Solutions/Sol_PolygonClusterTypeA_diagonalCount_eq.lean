-- Prove2me | solution 1 for PolygonClusterTypeA.diagonalCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:16:18.116508+00:00
-- url     : https://prove2.me/submissions/2dfc20c0-c331-4972-9b57-71342aba26d2

import Mathlib
import Definitions.Def_Geometry_GraphTheory_PolygonClusterTypeA
open PolygonClusterTypeA in
theorem solution (m : ℕ) (hm : 3 ≤ m) : diagonalCount m = m.choose 2 - m := by
  classical
  unfold diagonalCount diagonalFinset
  have hval : ∀ i : Fin m, ((nextV i : Fin m) : ℕ) = if (i : ℕ) + 1 < m then (i : ℕ) + 1 else 0 := by
    intro i
    show ((i : ℕ) + 1) % m = _
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · have : (i : ℕ) + 1 = m := by have := i.isLt; omega
      rw [this, Nat.mod_self]
  -- the non-diagonal pairs number `C(m, 2)`
  have hnd : (Finset.univ.filter (fun e : Sym2 (Fin m) => ¬ e.IsDiag)).card = m.choose 2 := by
    rw [← Fintype.card_subtype, Sym2.card_subtype_not_diag, Fintype.card_fin]
  -- the sides are the `m` distinct pairs `s(i, i+1)`
  have hsides : (Finset.univ.filter (fun e : Sym2 (Fin m) => ¬ e.IsDiag ∧ IsSide m e)).card = m := by
    have heq : Finset.univ.filter (fun e : Sym2 (Fin m) => ¬ e.IsDiag ∧ IsSide m e)
        = Finset.univ.image (fun i : Fin m => s(i, nextV i)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨-, i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        refine ⟨?_, i, rfl⟩
        rw [Sym2.mk_isDiag_iff]
        intro h
        have := congrArg Fin.val h
        rw [hval] at this
        split_ifs at this <;> omega
    rw [heq, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro i j hij
    rcases Sym2.eq_iff.mp hij with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      rw [hval] at e1 e2
      have := i.isLt
      have := j.isLt
      apply Fin.ext
      split_ifs at e1 e2 <;> omega
  -- non-diagonal pairs = sides + diagonals
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun e : Sym2 (Fin m) => ¬ e.IsDiag)) (fun e => IsSide m e)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  omega
