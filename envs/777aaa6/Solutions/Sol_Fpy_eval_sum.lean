-- Prove2me | solution 1 for Fpy.eval_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:49:16.185986+00:00
-- url     : https://prove2.me/submissions/3c808b57-9f05-4214-95aa-24fb03cf0f2b

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_FormatInference_Sum
import Theorems.Thm_Fpy_sumVal_mem
import Theorems.Thm_Fpy_exec_sumBody
import Theorems.Thm_Fpy_exists_map_num


set_option autoImplicit true
open Fpy
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
namespace Fpy
theorem _root_.solution (hA : A.Sound Φ) (hsum : Φ "sum" = some ("xs", sumBody)) {Γ : AEnv D}
    {κ : Option Val} {σ : Store} {C : Val} {r : Num → Num} {e : Expr (fpy decode)}
    {F : D.Fmt} {L : ℕ} {v : Val} (hΓ : Γ.Holds σ) (hκ : Admits κ C)
    (hr : C.rnd (fpy decode) = some r) (he : AEval A Φ Γ κ e (.list (.fmt F)))
    (hL : ∀ vs, Eval Φ σ C e (.list vs) → vs.length = L) (h : Eval Φ σ C (.call "sum" e) v) :
    Describes (.fmt (sumFmt A κ F L)) v := by
  cases h with
  | call hΦ he' hs =>
    rw [hsum] at hΦ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ)
    cases eval_sound hA he' hΓ hκ he with
    | list hall =>
      obtain ⟨us, rfl, hus⟩ := exists_map_num (P := (· ∈ D.γ F)) fun w hw => by
        cases describesAll_iff.mp hall w hw with | fmt hu => exact ⟨_, rfl, hu⟩
      obtain rfl := hL _ he'
      obtain ⟨⟩ := exec_sumBody hr hs
      rw [List.length_map]
      exact .fmt (sumVal_mem hA hκ hr hus)
end Fpy
