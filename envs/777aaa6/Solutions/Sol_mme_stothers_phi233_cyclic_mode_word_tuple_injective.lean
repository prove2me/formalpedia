-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_mode_word_tuple_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:33:29.798704+00:00
-- url     : https://prove2.me/submissions/b60b0eca-4798-4bb2-b70f-0bd697d565a8

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data

open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true

theorem solution :
    ∀ {N alpha beta gamma delta : ℕ},
      Function.Injective
        (cyclicModeWord (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) (delta := delta)) := by
  intro N alpha beta gamma delta e f hef
  rcases e with ⟨a, b, d⟩
  rcases f with ⟨a', b', d'⟩
  apply Prod.ext
  · apply Subtype.ext
    funext i j
    fin_cases i
    · exact congrFun (congrArg Prod.fst (congrFun hef 0)) j
    · exact congrFun (congrArg Prod.fst (congrFun hef 1)) j
    · exact congrFun (congrArg Prod.fst (congrFun hef 2)) j
  · apply Prod.ext
    · apply Subtype.ext
      funext i j
      fin_cases i
      · exact congrFun
          (congrArg (fun u ↦ u.2.1) (congrFun hef 1)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.1) (congrFun hef 2)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.1) (congrFun hef 0)) j
    · apply Subtype.ext
      funext i j
      fin_cases i
      · exact congrFun
          (congrArg (fun u ↦ u.2.2) (congrFun hef 2)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.2) (congrFun hef 0)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.2) (congrFun hef 1)) j
