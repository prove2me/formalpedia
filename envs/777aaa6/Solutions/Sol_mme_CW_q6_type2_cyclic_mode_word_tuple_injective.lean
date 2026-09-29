-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_mode_word_tuple_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:01:46.121758+00:00
-- url     : https://prove2.me/submissions/6257d864-7265-4eb8-a6c3-2d293f837a96

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_data

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution :
    ∀ {N L G : ℕ},
      Function.Injective
        (fun e : CWQ6Type2CyclicEdge N L G ↦
          cwQ6Type2CyclicModeWord e) := by
  intro N L G e f hef
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
