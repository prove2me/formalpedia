-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.path_replicate_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:23:00.057175+00:00
-- url     : https://prove2.me/submissions/69ee435b-09a1-4940-9b30-5fc1bdade9f0

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceLoops
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
omit [DecidableEq X]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution (θ : FreeGroup X →* Multiplicative ℝ)
    (z : X × Bool) (hz : step θ z ≤ 0) (n : ℕ) :
    PathIn (step θ) (fun x => x ≤ 0) 0 (List.replicate n z) := by
  have hgen : ∀ p : ℝ, p ≤ 0 →
      PathIn (step θ) (fun x => x ≤ 0) p (List.replicate n z) := by
    induction n with
    | zero => intro p hp; exact hp
    | succ n ih =>
      intro p hp
      exact ⟨hp, ih (p + step θ z) (by linarith)⟩
  exact hgen 0 le_rfl
end Kourovka.MetabelianEnumeration.SchreierHeights
