-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_leastPositiveResidue_pos_le
-- name    : ErdosProblems.Erdos269.leastPositiveResidue_pos_le
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:39:48.390977+00:00
-- url     : https://prove2.me/theorems/d91f8512-ecbc-4c82-b0b9-44050b23927d
-- title:
--   LeastPositiveResidue pos le
-- statement:
--   For positive modulus C, the least positive residue lies between 1 and C inclusive.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/ResidueEscape.lean#L29-L48
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Erdős #269: the finite least-positive-residue obstruction

For a positive modulus `C`, the least positive representative of a congruence
class is `C` for the zero class and lies in `1, ..., C - 1` otherwise.  Hence a
positive integer state bounded by `K` cannot be congruent to an integer whose
least positive representative is larger than `K`.

This module proves only that final finite obstruction.  An application to the
series in Erdős problem #269 still needs two upstream inputs: rationality must
produce a positive bounded integral state with the required smooth-divisibility
congruence, and one must construct arbitrarily late finite windows whose least
positive residues escape the corresponding bound.  Neither input, and hence no
irrationality theorem for the series, is proved here.
-/

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.leastPositiveResidue_pos_le
    {C : ℕ} (hC : 0 < C) (x : ℤ) :
    0 < leastPositiveResidue C x ∧ leastPositiveResidue C x ≤ C := by sorry
