-- Prove2me | solution 1 for HilbertChess.mate_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:10:23.986604+00:00
-- url     : https://prove2.me/submissions/c1078f80-876f-4b25-9b08-971f7cf5b8f3

import Mathlib
import Definitions.Def_Geometry_HilbertChessLines
open HilbertChess in
theorem solution (p : Square) : ∃ S : List Line, S.length = 3 ∧ Checkmated S p := by
  -- three horizontal lines through the king's three rows
  let row : ℤ → Line := fun t => ⟨0, 1, p.2 + t, Or.inr one_ne_zero⟩
  have hrow : ∀ t : ℤ, ∀ q : Square, q.2 = p.2 + t → (row t).covers q := by
    intro t q hq
    show 0 * q.1 + 1 * q.2 = p.2 + t
    rw [hq]
    ring
  refine ⟨[row (-1), row 0, row 1], rfl, ?_, ?_⟩
  · exact ⟨row 0, by simp, hrow 0 p (by ring)⟩
  · intro d hd
    have hd2 : d.2 ∈ ({-1, 0, 1} : Finset ℤ) := by
      rw [kingMoves, Finset.mem_erase, blockOffsets, Finset.mem_product] at hd
      exact hd.2.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd2
    rcases hd2 with h | h | h
    · exact ⟨row (-1), by simp, hrow (-1) _ (by simp [h])⟩
    · exact ⟨row 0, by simp, hrow 0 _ (by simp [h])⟩
    · exact ⟨row 1, by simp, hrow 1 _ (by simp [h])⟩
