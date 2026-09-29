-- Prove2me | solution 1 for mme_released_116_six_region_joint_counts_exact
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T12:59:34.518987+00:00
-- url     : https://prove2.me/submissions/158e17bc-37c5-457e-8a3f-8ace3be09840

import Definitions.Def_mme_released_116_six_region_reconstruction

theorem solution :
 MME.Released116.reconstructed = (MME.ReleasedGlobal.jointRows 0 10).map (fun p => (p.1.val, p.2)) := by decide
#print axioms solution
