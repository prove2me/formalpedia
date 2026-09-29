-- Prove2me | solution 1 for mme_stothers_phi134_cyclic_mode_word_tuple_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:57:16.036872+00:00
-- url     : https://prove2.me/submissions/def6d834-2ac7-4a9c-b18e-dc0368d58c5b

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

theorem solution :
    ∀ {N alpha beta gamma delta : ℕ},
      Function.Injective
        (cyclicModeWord (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) (delta := delta)) := by
  intro N alpha beta gamma delta e f hef
  rcases e with ⟨a, b, c⟩
  rcases f with ⟨a', b', c'⟩
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    funext i j
    fin_cases i
    · exact congrFun (congrArg Prod.fst (congrFun hef 0)) j
    · exact congrFun (congrArg Prod.fst (congrFun hef 1)) j
    · exact congrFun (congrArg Prod.fst (congrFun hef 2)) j
  · apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      funext i j
      fin_cases i
      · exact congrFun
          (congrArg (fun u ↦ u.2.1) (congrFun hef 1)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.1) (congrFun hef 2)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.1) (congrFun hef 0)) j
    · apply Subtype.ext
      apply Subtype.ext
      funext i j
      fin_cases i
      · exact congrFun
          (congrArg (fun u ↦ u.2.2) (congrFun hef 2)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.2) (congrFun hef 0)) j
      · exact congrFun
          (congrArg (fun u ↦ u.2.2) (congrFun hef 1)) j
