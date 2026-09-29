-- Prove2me | solution 1 for TropicalLA.exists_repeat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:34:41.757532+00:00
-- url     : https://prove2.me/submissions/022f898a-950b-4612-ad8c-bfc9cbca9bf6

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] (p : ℕ → ι) :
    ∃ a b : ℕ, a < b ∧ b ≤ Fintype.card ι ∧ p a = p b := by
  -- pigeonhole on the first `card ι + 1` terms
  have hcard : Fintype.card ι < Fintype.card (Fin (Fintype.card ι + 1)) := by
    simp
  obtain ⟨x, y, hxy, hpe⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (Fintype.card ι + 1) => p (k : ℕ)) hcard
  rcases lt_or_gt_of_ne (fun h : (x : ℕ) = (y : ℕ) => hxy (Fin.ext h)) with hlt | hlt
  · exact ⟨x, y, hlt, by omega, hpe⟩
  · exact ⟨y, x, hlt, by omega, hpe.symm⟩
