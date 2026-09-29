-- Prove2me | solution 1 for actGen_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T19:29:02.830631+00:00
-- url     : https://prove2.me/submissions/9e13099e-7bf2-4231-bfbe-d760be5e325e

import Mathlib
import Definitions.Def_Cryptography_PosetTheory_BerggrenGreenIncomparability

set_option linter.unusedVariables false

theorem solution (g : BergGen) : Function.Injective (actGen g) := by
  intro p q h
  cases g with
  | A =>
      have h2 : p.1 = q.1 := by simpa [actGen] using congrArg Prod.snd h
      have h1 : 2 * p.1 - p.2 = 2 * q.1 - q.2 := by
        simpa [actGen] using congrArg Prod.fst h
      have : p.2 = q.2 := by linarith [h1, h2]
      exact Prod.ext h2 this
  | B =>
      have h2 : p.1 = q.1 := by simpa [actGen] using congrArg Prod.snd h
      have h1 : 2 * p.1 + p.2 = 2 * q.1 + q.2 := by
        simpa [actGen] using congrArg Prod.fst h
      have : p.2 = q.2 := by linarith [h1, h2]
      exact Prod.ext h2 this
  | C =>
      have h2 : p.2 = q.2 := by simpa [actGen] using congrArg Prod.snd h
      have h1 : p.1 + 2 * p.2 = q.1 + 2 * q.2 := by
        simpa [actGen] using congrArg Prod.fst h
      have : p.1 = q.1 := by linarith [h1, h2]
      exact Prod.ext this h2
