-- Prove2me | solution 1 for evalBergWord_append
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:52:17.732575+00:00
-- url     : https://prove2.me/submissions/15b3cf12-f5f1-40d2-8114-2e1aa21dc2b1

import Mathlib
import Definitions.Def_Cryptography_PosetTheory_BerggrenGreenIncomparability
theorem solution (u v : BergWord) :
    evalBergWord (u ++ v) = evalBergWord u * evalBergWord v := by
  induction u with
  | nil => simp [evalBergWord]
  | cons g u ih =>
    simp only [List.cons_append, evalBergWord, ih, mul_assoc]
