-- Prove2me | solution 1 for ProofSearchFractalDimension.dim_codimension_density
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T16:21:38.574084+00:00
-- url     : https://prove2.me/submissions/a56f2593-d888-4c54-b2ba-1af4cc599774

import Mathlib
import Definitions.Def_Bridges_ProofSearchFractalDimension
open ProofSearchFractalDimension in
theorem solution (b s n : ℕ) (hb : 1 < b) (hs : 1 ≤ s) :
    (((s : ℝ)) / ((b : ℝ))) ^ n = ((totalPaths b n : ℝ)) ^ (searchDim b s - 1) := by
  unfold totalPaths searchDim
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  push_cast
  -- both sides are `exp (n (log s - log b))`
  rw [Real.rpow_def_of_pos (pow_pos hb0 n), Real.log_pow,
    ← Real.exp_log (pow_pos (div_pos hs0 hb0) n), Real.log_pow, Real.log_div hs0.ne' hb0.ne']
  congr 1
  field_simp
