-- Prove2me | solution 2 for EscapeCriterion.filledJulia_qmap_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:54:59.748496+00:00
-- url     : https://prove2.me/submissions/65f4ac3b-9753-4a94-a009-848502e5b079

import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_FilledJuliaCompact
import Definitions.Def_Novelty_MandelbrotQuadraticEscape
open EscapeCriterion in
theorem solution (c z : ℂ) : z ∈ filledJulia c ↔ MandelbrotEscape.qmap c z ∈ filledJulia c := by
  have hshift : ∀ n, orbit c (MandelbrotEscape.qmap c z) n = orbit c z (n + 1) := by
    intro n
    unfold orbit
    rw [Function.iterate_succ_apply]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, fun n => by rw [hshift]; exact hB (n + 1)⟩
  · rintro ⟨B, hB⟩
    refine ⟨max B ‖z‖, fun n => ?_⟩
    cases n with
    | zero => simp [orbit]
    | succ n =>
      rw [← hshift]
      exact (hB n).trans (le_max_left _ _)
