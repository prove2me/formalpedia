-- Prove2me | solution 1 for Fpy.Atom.holds_refine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:37:57.600283+00:00
-- url     : https://prove2.me/submissions/9e335973-5a87-476d-aa18-7d5f32d13564

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
import Theorems.Thm_Fpy_Atom_mem_narrowFmt

set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}
variable {c : Ceiling}
namespace Fpy
namespace Atom
theorem _root_.solution {a : Atom} {b : Bool} {Γ : AEnv (Fmt.domain c)} {σ : Store}
    (hΓ : Γ.Holds σ) {u : Num} (hx : σ a.x = some (.num u)) (ha : a.Holds u b) :
    (a.refine b Γ).Holds σ := by
  unfold Atom.refine
  split
  · next F hF =>
    obtain ⟨v, hv, hd⟩ := hΓ _ _ hF
    rw [hx, Option.some.injEq] at hv
    subst hv
    cases hd with
    | fmt hu =>
      have := hΓ.update a.x (Describes.fmt (D := Fmt.domain c) (a.mem_narrowFmt hu ha))
      rwa [Store.update, ← hx, Function.update_eq_self] at this
  · exact hΓ
end Atom
end Fpy
