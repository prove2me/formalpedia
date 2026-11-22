-- Prove2me | solution 1 for Fpy.mem_lift1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:28:03.218856+00:00
-- url     : https://prove2.me/submissions/257830a1-62a7-4825-8a96-d294091cffa5

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops

set_option autoImplicit true
open Fpy
open Mpfx
variable (c : Ceiling)
variable {c}
namespace Fpy
theorem _root_.solution {f : Num → Num} {fa : Format → Fmt}
    (ha : ∀ {F u}, u ∈ F.reals → f u ∈ (fa F).γ) {F : Fmt} {u : Num} (hu : u ∈ F.γ) :
    f u ∈ (lift1 f fa F).γ := by
  classical
  cases F with
  | set S => exact Finset.mem_image_of_mem f hu
  | abs F => exact ha hu
  | top => trivial
end Fpy
