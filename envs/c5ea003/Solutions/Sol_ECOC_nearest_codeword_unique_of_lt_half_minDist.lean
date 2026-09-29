-- Prove2me | solution 1 for ECOC.nearest_codeword_unique_of_lt_half_minDist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:05:43.364434+00:00
-- url     : https://prove2.me/submissions/333ab08c-760d-44fc-b0d4-e56ce6609f34

-- Sol generated from Bridges/HammingCode.lean
import Mathlib
import Definitions.Def_Bridges_HammingCode

open Finset

open ECOC







open ECOC in
theorem solution    {n m δ : ℕ} {code : Fin n → Fin m → Bool} {y : Fin m → Bool} {c : Fin n}
    (hδ : MinDistAtLeast code δ)
    (hy : 2 * _root_.hammingDist y (code c) < δ) :
    nearestUnique code y c := by
  intro c' hc'
  have hmin : δ ≤ _root_.hammingDist (code c) (code c') := hδ hc'.symm
  have htri : _root_.hammingDist (code c) (code c') ≤
      _root_.hammingDist y (code c) + _root_.hammingDist y (code c') := by
    simpa [_root_.hammingDist_comm] using
      (_root_.hammingDist_triangle_left (code c) (code c') y)
  have hdef : ∀ (x x' : Fin m → Bool), ECOC.hammingDist x x' = _root_.hammingDist x x' :=
    fun _ _ => rfl
  show ECOC.hammingDist y (code c) < ECOC.hammingDist y (code c')
  rw [hdef, hdef]
  omega
