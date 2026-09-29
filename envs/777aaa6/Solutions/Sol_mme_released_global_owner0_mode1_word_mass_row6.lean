-- Prove2me | solution 1 for mme_released_global_owner0_mode1_word_mass_row6
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T00:08:20.055749+00:00
-- url     : https://prove2.me/submissions/b141399c-8c81-4e8e-bcc2-337c4bd22c61

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The exact released global word masses in coordinate pool 6 agree with the corresponding rational table row. This certifies the table identity used in the outer word entropy bound. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8233862731364122285621661424410707841378990000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234866846055627639581546072900290584317242020000000000000, 0, 0, 0, 0, 0, 289206475665156706684852851768514000000000000000000000000, 0, 289206475656140744788852851768514000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8233862643677294364621661424410707841378990000000000000, 0, 0, 0, 0, 0, 289206475493129540706852851768514000000000000000000000000, 0, 289206475614676015469852851768514000000000000000000000000, 0, 0, 0, 8238231247853901417860225292823362354565060000000000000, 0, 235079133755139345929078746591185275290869880000000000000, 0, 8238231137234688770860225292823362354565060000000000000, 0, 0] : List ℕ).getD
      (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) /
      1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 6 then
      ((alpha 0 s * ((jointRows 0 s).map
        (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
