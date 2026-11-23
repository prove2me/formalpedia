-- Prove2me | Theorems.Thm_choueka_lemma
-- name    : choueka_lemma
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:49:23.777313+00:00
-- url     : https://prove2.me/theorems/7f91d9d1-8938-4d0c-837b-8119a4d96f4c
-- title:
--   choueka lemma: choueka lemma
-- statement:
--   The Choueka lemma, which converts an ω-power to the concatenation of a
--   Kleene star followed by an ω-limit, the latter of which is a natural fit for
--   deterministic Muller automata.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L251-L256
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L251-L256

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}

theorem choueka_lemma [Inhabited A] {L : Set (List A)}
    (h : RegLang L) : ∃ L' : Set (List A), RegLang L' ∧ L^ω = L∗  * L'↗ω := by sorry
