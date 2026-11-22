-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.rewrite_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:35.442204+00:00
-- url     : https://prove2.me/submissions/dcd2121c-d817-4228-9423-1480cecc6c3b

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting

set_option autoImplicit true
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]
namespace Kourovka.Schreier.Transversal
theorem _root_.solution (p : FreeGroup X) (xs : List (X × Bool)) :
    S.rewrite p (FreeGroup.mk xs) = S.rewriteWord p xs := rfl
end Kourovka.Schreier.Transversal
