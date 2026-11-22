-- Prove2me | solution 1 for Fpy.DigitBound.le_num
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:46:47.584957+00:00
-- url     : https://prove2.me/submissions/25b74dca-92c8-4337-a817-ae50901cc378

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Join
import Theorems.Thm_Fpy_DigitBound_NumIn_eq
import Theorems.Thm_Fpy_DigitBound_eval_update
import Theorems.Thm_Fpy_DigitBound_fresh_numIn


set_option autoImplicit true
open Fpy Fpy.DigitBound
namespace Fpy.DigitBound
theorem _root_.solution {Ψg : List Con} {n : ℕ} {l m Lo Hi : Term} {τ : Option Term} (hLo : Lo.Below n)
    (hHi : Hi.Below n) (hl : ∀ ι, Lo.eval ι ≤ l.eval ι) (hm : ∀ ι, m.eval ι ≤ Hi.eval ι) :
    DVal.Le n (n + 2) Ψg (bounds n Lo Hi (hLo.mono (Nat.le_succ n)) hHi) (.num l m τ)
      (.num (.var (n + 1)) (.var n) none) := by
  intro _ ι v _ hd
  cases hd with
  | num hu =>
    obtain ⟨ι', a, hs, hw⟩ := fresh_numIn (hLo.mono (Nat.le_succ n)) hHi ι _ fun hn => by
      obtain ⟨hl', hm'⟩ := hu.eq hn
      rw [eval_update hLo, hl', hm']
      exact ⟨hm ι, hl ι⟩
    exact ⟨ι', a, hs, .num hw⟩
end Fpy.DigitBound
