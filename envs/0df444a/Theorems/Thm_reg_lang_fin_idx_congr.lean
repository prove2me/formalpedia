-- Prove2me | Theorems.Thm_reg_lang_fin_idx_congr
-- name    : reg_lang_fin_idx_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:30:46.623586+00:00
-- url     : https://prove2.me/theorems/e4d21364-3cb8-4d42-8243-a2315074083f
-- title:
--   reg lang fin idx congr: reg lang fin idx congr
-- statement:
--   If a (right) congruence is of finite index,
--   then each of its equivalence classes is regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L203-L208
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L203-L208

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}

theorem reg_lang_fin_idx_congr [Inhabited A] {c : Congruence A}
    (h : Finite (c.QuotType)) (s : c.QuotType) : RegLang (c.EqvCls s) := by sorry
