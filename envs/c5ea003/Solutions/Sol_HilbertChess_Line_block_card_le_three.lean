-- Prove2me | solution 1 for HilbertChess.Line.block_card_le_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:06:09.599106+00:00
-- url     : https://prove2.me/submissions/181a762e-2d46-404d-a0d0-4c3ec137f8ad

import Mathlib
import Definitions.Def_Geometry_HilbertChessLines
open HilbertChess in
theorem solution (L : Line) (p : Square) : (L.blockCovered p).card ≤ 3 := by
  have h3 : ({-1, 0, 1} : Finset ℤ).card = 3 := by decide
  have hmem : ∀ d ∈ L.blockCovered p, d.1 ∈ ({-1, 0, 1} : Finset ℤ) ∧
      d.2 ∈ ({-1, 0, 1} : Finset ℤ) ∧ L.a * (p.1 + d.1) + L.b * (p.2 + d.2) = L.c := by
    intro d hd
    rw [Line.blockCovered, Finset.mem_filter] at hd
    obtain ⟨hdo, hcov⟩ := hd
    rw [blockOffsets, Finset.mem_product] at hdo
    exact ⟨hdo.1, hdo.2, hcov⟩
  by_cases hb : L.b = 0
  · -- a vertical line: the column offset determines the square
    have ha : L.a ≠ 0 := L.nondeg.resolve_right (not_not.mpr hb)
    rw [← h3]
    apply Finset.card_le_card_of_injOn (fun d : Square => d.2)
    · intro d hd
      exact (hmem d hd).2.1
    · intro d hd d' hd' heq
      have e1 := (hmem d hd).2.2
      have e2 := (hmem d' hd').2.2
      rw [hb] at e1 e2
      have h1 : L.a * (p.1 + d.1) = L.a * (p.1 + d'.1) := by linarith
      have h2 := mul_left_cancel₀ ha h1
      exact Prod.ext (by linarith) heq
  · -- otherwise the row offset determines the square
    rw [← h3]
    apply Finset.card_le_card_of_injOn (fun d : Square => d.1)
    · intro d hd
      exact (hmem d hd).1
    · intro d hd d' hd' heq
      have e1 := (hmem d hd).2.2
      have e2 := (hmem d' hd').2.2
      have heq' : d.1 = d'.1 := heq
      rw [heq'] at e1
      have h1 : L.b * (p.2 + d.2) = L.b * (p.2 + d'.2) := by linarith
      have h2 := mul_left_cancel₀ hb h1
      exact Prod.ext heq' (by linarith)
