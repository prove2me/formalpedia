-- Prove2me | solution 1 for Fpy.Atom.mem_narrowFmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:36:34.695679+00:00
-- url     : https://prove2.me/submissions/7e1dc03c-5bdc-452c-aa97-a3a8075ba6b4

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
import Theorems.Thm_Fpy_Atom_reals_narrow

set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}
namespace Fpy
namespace Atom
theorem _root_.solution {a : Atom} {b : Bool} {F : Fmt} {u : Num} (hu : u ∈ F.γ)
    (ha : a.Holds u b) : u ∈ (a.narrowFmt b F).γ := by
  classical
  cases F with
  | set S => exact Finset.mem_filter.mpr ⟨hu, ha⟩
  | abs F => exact a.reals_narrow hu ha
  | top => trivial
end Atom
end Fpy
