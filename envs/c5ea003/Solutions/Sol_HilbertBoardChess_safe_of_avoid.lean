-- Prove2me | solution 1 for HilbertBoardChess.safe_of_avoid
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T07:15:36.97415+00:00
-- url     : https://prove2.me/submissions/76a9cdf8-dbec-40fe-8033-6e6665e5de9a

import Mathlib
import Definitions.Def_Applications_HilbertSpace_HilbertBoardChess
open HilbertBoardChess in
theorem solution {d : ℕ} (R : Finset (Sq d)) (x y : ℤ)
    (hx : x ∉ R.image (fun r => r 0)) (hy : y ∉ R.image (fun r => r 1)) :
    ¬ attackedBy R (fun i => if i = 0 then x else if i = 1 then y else 0) := by
  rintro ⟨r, hr, -, j, hj⟩
  have h01 : (0 : Fin (d + 2)) ≠ 1 := by simp [Fin.ext_iff]
  -- a rook attack agrees with the rook off one coordinate `j`; coordinate `0` or `1` survives
  by_cases hj0 : (0 : Fin (d + 2)) = j
  · have h1 := hj 1 (fun h => h01 (hj0.trans h.symm))
    simp only [if_neg h01.symm, if_true] at h1
    exact hy (Finset.mem_image.mpr ⟨r, hr, h1.symm⟩)
  · have h0 := hj 0 hj0
    simp only [if_true] at h0
    exact hx (Finset.mem_image.mpr ⟨r, hr, h0.symm⟩)
