-- Prove2me | solution 1 for Fpy.DigitBound.foldl_add_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:44:44.50122+00:00
-- url     : https://prove2.me/submissions/f9c95ac3-4126-46c2-aadc-f1ccfdc41b23

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution {P : ℕ → Num → Prop} {Q : Num → Prop}
    (hstep : ∀ k s w, P k s → Q w → P (k + 1) (Num.add s w)) :
    ∀ (ws : List Num) (k : ℕ) (s : Num), P k s → (∀ w ∈ ws, Q w) →
      P (k + ws.length) (ws.foldl (fun s w => id (Num.add s w)) s)
  | [], _, _, h, _ => h
  | w :: ws, k, s, h, hws => by
    have := solution hstep ws (k + 1) _ (hstep k s w h (hws w (List.mem_cons_self ..)))
      fun w' h' => hws w' (List.mem_cons_of_mem _ h')
    rwa [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]
end Fpy.DigitBound
