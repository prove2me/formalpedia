-- Prove2me | solution 1 for mme_alphaevolve_level4_global_graded_surplus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-29T20:45:11.911212+00:00
-- url     : https://prove2.me/submissions/df23556f-cab2-48a5-a81b-bfbfeb3f4967
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_global_CW_graded_start_data
import Theorems.Thm_mme_alphaevolve_level4_global_graded_log_margin_certificate

open MME MME.GlobalCW
set_option autoImplicit false

theorem solution :
    Exists fun n : Nat => Exists fun D : GlobalCW.StartG (8 * n) 4 =>
      And (0 < n) (And (1 <= D.inputs) (And (1 <= D.a * D.b * D.c)
        (((D.inputs * 7 ^ (8 * n) : Nat) : Real) <
          Real.exp D.logOutputs *
            (((D.a * D.b * D.c : Nat) : Real) ^ ((2371177 : Real) / 3000000))))) := by
  obtain ⟨n, D, hn, hinputs, hdims, hmargin⟩ :=
    mme_alphaevolve_level4_global_graded_log_margin_certificate
  refine ⟨n, D, hn, hinputs, hdims, ?_⟩
  have hpow : Real.exp (((8 * n : Nat) : Real) * Real.log 7) = (7 : Real) ^ (8 * n) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hleft :
      Real.exp (Real.log (D.inputs : Real) + ((8 * n : Nat) : Real) * Real.log 7) =
        ((D.inputs * 7 ^ (8 * n) : Nat) : Real) := by
    rw [Real.exp_add, Real.exp_log (by positivity), hpow]
    norm_cast
  have hright :
      Real.exp (D.logOutputs + ((2371177 : Real) / 3000000) *
          Real.log ((D.a * D.b * D.c : Nat) : Real)) =
        Real.exp D.logOutputs *
          (((D.a * D.b * D.c : Nat) : Real) ^ ((2371177 : Real) / 3000000)) := by
    rw [Real.exp_add]
    congr 1
    calc
      Real.exp (((2371177 : Real) / 3000000) *
          Real.log ((D.a * D.b * D.c : Nat) : Real)) =
        Real.exp (Real.log ((D.a * D.b * D.c : Nat) : Real) *
          ((2371177 : Real) / 3000000)) := by congr 1 <;> ring
      _ = ((D.a * D.b * D.c : Nat) : Real) ^ ((2371177 : Real) / 3000000) := by
        rw [← Real.rpow_def_of_pos (by positivity)]
  have h := Real.exp_lt_exp.mpr hmargin
  rw [hleft, hright] at h
  exact h
