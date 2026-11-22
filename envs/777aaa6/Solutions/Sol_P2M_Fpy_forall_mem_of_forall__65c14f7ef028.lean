-- Prove2me | solution 1 for P2M_Fpy_forall_mem_of_forall__65c14f7ef028
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:52:09.595345+00:00
-- url     : https://prove2.me/submissions/8677ec18-628b-442f-90c3-5a23793ab648

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
namespace Fpy
theorem _root_.solution {S : Set Num} :
    ∀ {us : List Num} {Fs : List D.Fmt}, List.Forall₂ (fun u F => u ∈ D.γ F) us Fs →
      (∀ F ∈ Fs, D.γ F ⊆ S) → ∀ u ∈ us, u ∈ S
  | _, _, .nil, _, _, hu => absurd hu List.not_mem_nil
  | _, _, .cons hu hs, hS, _, hu' => (List.mem_cons.mp hu').elim
      (fun h => h ▸ hS _ (List.mem_cons_self ..) hu)
      (solution hs (fun F hF => hS F (List.mem_cons_of_mem _ hF)) _)
end Fpy
