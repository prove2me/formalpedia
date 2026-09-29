-- Prove2me | solution 1 for Teichmuller.LinMap.dil_eq_sq_div_jac
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T09:01:32.196932+00:00
-- url     : https://prove2.me/submissions/88dcf8b6-8c08-4a67-979b-3acf153dfd72

import Definitions.Def_Geometry_Teichmuller_LinearQC
open Teichmuller in
theorem solution (f : LinMap) : f.dil = (‖f.a‖ + ‖f.b‖) ^ 2 / f.jac := by
  have hj := f.jac_pos
  have hlt := f.norm_lt
  have hd : 0 < ‖f.a‖ - ‖f.b‖ := by linarith
  rw [LinMap.dil, div_eq_div_iff hd.ne' hj.ne', LinMap.jac]
  ring
