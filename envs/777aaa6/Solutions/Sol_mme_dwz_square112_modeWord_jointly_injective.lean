-- Prove2me | solution 1 for mme_dwz_square112_modeWord_jointly_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-08T08:19:21.785509+00:00
-- url     : https://prove2.me/submissions/8db7b70b-5575-4d38-ae52-af6a42fb4605

import Definitions.Def_mme_dwz_square112_exact_profile_data
open MME.DWZSquare112
set_option autoImplicit false

theorem solution (N : ℕ) (c : Fin 4 → ℕ) :
    Function.Injective
      (fun w : ExactWord N c => (fun i => modeWord w i : Fin 3 → Fin N → Fin 3)) := by
  have hrow : Function.Injective row := by decide
  intro w₁ w₂ h
  apply Subtype.ext
  funext j
  apply hrow
  funext i
  exact congrFun (congrFun h i) j
