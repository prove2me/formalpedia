-- Prove2me | solution 1 for ErdosProblems.Erdos269.leastPositiveResidue_pos_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:39:55.859391+00:00
-- url     : https://prove2.me/submissions/441b5d2f-3bce-4681-968a-0fea06cae629

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

open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {C : ℕ} (hC : 0 < C) (x : ℤ) :
    0 < leastPositiveResidue C x ∧ leastPositiveResidue C x ≤ C := by
  unfold leastPositiveResidue
  by_cases hx : x % (C : ℤ) = 0
  · simp [hx, hC]
  · simp only [hx, if_false]
    have hCInt : (0 : ℤ) < C := by exact_mod_cast hC
    have hnonneg : 0 ≤ x % (C : ℤ) :=
      Int.emod_nonneg x hCInt.ne'
    have hlt : x % (C : ℤ) < C :=
      Int.emod_lt_of_pos x hCInt
    constructor
    · exact Int.natAbs_pos.mpr hx
    · have habsLt : Int.natAbs (x % (C : ℤ)) < C := by
        exact_mod_cast (show (Int.natAbs (x % (C : ℤ)) : ℤ) < C by
          simpa [Int.natAbs_of_nonneg hnonneg] using hlt)
      omega
