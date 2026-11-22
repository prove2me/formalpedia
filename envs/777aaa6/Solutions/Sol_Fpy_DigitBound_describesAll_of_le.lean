-- Prove2me | solution 1 for Fpy.DigitBound.describesAll_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:24:15.266261+00:00
-- url     : https://prove2.me/submissions/c7288f5d-70a2-43ce-a993-0e2761aff8cd

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
import Theorems.Thm_Fpy_DigitBound_AgreeOut_agree

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution {n₀ n₁ : ℕ} {Ψ Ψ' : List Con} {d : DVal} {ι ι' : Asgn}
    (hb : Before n₀ Ψ) (hs : Sat ι Ψ) (h : Agree n₀ ι ι') :
    ∀ {ds : List DVal} {vs : List Val}, List.Forall₂ (Describes Ψ ι) ds vs →
      (∀ d' ∈ ds, DVal.Le n₀ n₁ Ψ Ψ' d' d) → DescribesAll (Ψ ++ Ψ') ι' d n₀ vs
  | _, _, .nil, _ => .nil
  | _, _, .cons hd tl, hle => by
    obtain ⟨ι₁, a₁, hs₁, hd'⟩ := hle _ (List.mem_cons_self ..) hb _ _ hs hd
    exact .cons (fun x hx => (h x hx).symm.trans (a₁.agree x hx))
      ((Sat.congr hb a₁.agree hs).append hs₁) hd'
      (solution hb hs h tl fun d' hd' => hle d' (List.mem_cons_of_mem _ hd'))
end Fpy.DigitBound
