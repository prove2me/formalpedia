-- Prove2me | solution 1 for Mpfx.Format.subset_unbounded_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:07.151057+00:00
-- url     : https://prove2.me/submissions/e5bc2c34-d6af-4d0b-9abb-b9c0885c294c

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Format_containsPrec

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F G : Format}
    (hp : G.p ≤ F.p) (he : F.exp ≤ G.exp) (hs : G.specials ⊆ F.specials) :
    G ⊆ F.unbounded :=
  containsPrec hp he le_top hs
end Mpfx.Format
