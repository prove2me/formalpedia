-- Prove2me | solution 1 for ErdosProblems.Erdos269.leastPositiveResidue_modEq
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:39:55.171113+00:00
-- url     : https://prove2.me/submissions/20e9762e-2831-45ad-9025-bca8cc0b28a1

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
    Int.ModEq C (leastPositiveResidue C x : ℤ) x := by
  unfold leastPositiveResidue Int.ModEq
  by_cases hx : x % (C : ℤ) = 0
  · simp [hx]
  · simp only [hx, if_false]
    have hCInt : (0 : ℤ) < C := by exact_mod_cast hC
    have hnonneg : 0 ≤ x % (C : ℤ) :=
      Int.emod_nonneg x hCInt.ne'
    have hlt : x % (C : ℤ) < C :=
      Int.emod_lt_of_pos x hCInt
    have hcast :
        ((Int.natAbs (x % (C : ℤ)) : ℕ) : ℤ) =
          x % (C : ℤ) := by
      simp [Int.natAbs_of_nonneg hnonneg]
    rw [hcast, Int.emod_eq_of_lt hnonneg hlt]
