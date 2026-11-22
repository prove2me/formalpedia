-- Prove2me | solution 1 for Fpy.denotes_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:37:12.274171+00:00
-- url     : https://prove2.me/submissions/14cfeff3-9938-4249-b15a-a265a6bd53f0

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
namespace Fpy
theorem _root_.solution : Denotes Φ .real .real :=
  fun _ _ => ⟨fun h => by cases h; rfl, fun h => by subst h; exact .real⟩
end Fpy
