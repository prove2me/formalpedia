-- Prove2me | solution 2 for mme_CW_subrank_capacity_poly_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-01T15:15:54.70001+00:00
-- url     : https://prove2.me/submissions/eb82bb81-587a-4115-a001-8ba2623e76d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_laser_witness_wz
import Theorems.Thm_mme_laser_value_lower_bound_wz_poly
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_subrank_capacity_poly

open MME

universe u

/-- **Sketch for `mme_CW_subrank_capacity_poly_lower`** — *real-formula version*.

Routes through the `_wz_poly` chain:

  `mme_CW_laser_witness_wz`  →  `5/2 ≤ laserValueFormula_wz G S`
  `mme_laser_value_lower_bound_wz_poly`  →  `laserValueFormula_wz G S ≤ subrankCapacityPoly (CWObj K 6)`
  ──────────────────────────────────────────
  `5/2 ≤ subrankCapacityPoly (CWObj K 6)`

Both children are Open (real, not vacuous) — this is a HONEST
SKETCH_ACCEPTED reduction that can propagate to PROVED once the two
imported `_wz` theorems are closed.

**Supersedes** today's earlier sketch (which exploited the
`laserValueFormula := 1` placeholder via `exfalso; linarith` and was
provably-irreducible). See `REPORT_placeholder_issue.md`. -/
theorem solution {K : Type u} [Field K] :
    (5 : ℝ) / 2 ≤ subrankCapacityPoly (CWObj K 6) := by
  obtain ⟨G, S, hSym, hSupp, hVal⟩ := mme_CW_laser_witness_wz (K := K)
  exact hVal.trans (mme_laser_value_lower_bound_wz_poly G S hSym hSupp)
