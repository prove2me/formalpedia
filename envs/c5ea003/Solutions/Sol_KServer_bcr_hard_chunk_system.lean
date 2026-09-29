-- Prove2me | solution 1 for KServer.bcr_hard_chunk_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-04T23:12:24.907762+00:00
-- url     : https://prove2.me/submissions/a34e7f7d-107a-45b8-b991-5458dca3afb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Theorems.Thm_KServer_chunk_system_pad
import Theorems.Thm_KServer_bcr_chunk_system_family

/-!
Hard chunk systems on exactly `k+1` points, obtained from the family on spaces of at most
`k+1` points by padding.
-/

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ (m : MetricSpace (Fin (k + 1))) (s t : Fin (k + 1)) (cHi T price : ℝ) (M : ℕ),
        0 ≤ price ∧
        0 < @dist (Fin (k + 1)) m.toDist s t ∧
        c * Real.log k ^ 2 * @dist (Fin (k + 1)) m.toDist s t ≤ T ∧
        Nonempty (@KServer.ChunkSystemB (Fin (k + 1)) m s t 0 cHi T price M) := by
  classical
  obtain ⟨c, hc, k₀, hk⟩ := KServer.bcr_chunk_system_family
  refine ⟨c, hc, k₀, ?_⟩
  intro k hkk
  obtain ⟨X, mX, fX, s, t, hcard, hdpos, cHi, T, price, M, C, hprice, hT, h0triv⟩ := hk k hkk
  letI := mX
  letI := fX
  obtain ⟨m, a, b, hab, C', -, -⟩ :=
    KServer.chunk_system_pad (X := X) (s := s) (t := t) k hcard C h0triv
      (V := ∑ ω, C.P ω * ((∑ i, C.size ω i)
        - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2) le_rfl
  refine ⟨m, a, b, cHi, T, price, M, hprice, ?_, ?_, ⟨C'⟩⟩
  · rw [hab]; exact hdpos
  · rw [hab]; exact hT
