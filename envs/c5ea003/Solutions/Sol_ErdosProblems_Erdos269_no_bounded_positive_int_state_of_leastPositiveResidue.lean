-- Prove2me | solution 1 for ErdosProblems.Erdos269.no_bounded_positive_int_state_of_leastPositiveResidue
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:41:54.50927+00:00
-- url     : https://prove2.me/submissions/276a5060-8a4f-4447-bbfc-d2130f5e546b

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Theorems.Thm_ErdosProblems_Erdos269_leastPositiveResidue_modEq
import Theorems.Thm_ErdosProblems_Erdos269_leastPositiveResidue_pos_le
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

namespace ErdosProblems.Erdos269
/-- No positive state bounded by `bound` can represent, modulo `C`, a residue
in the canonical positive range that lies above `bound`. -/
theorem no_bounded_positive_state_of_residue_escape
    {C bound residue c : ℕ}
    (hcpos : 0 < c)
    (hcbound : c ≤ bound)
    (hescape : ResidueEscapesWindow C bound residue)
    (hmod : c % C = residue % C) :
    False := by
  rcases hescape with ⟨hboundResidue, hresidueC⟩
  have hcC : c < C :=
    lt_of_le_of_lt hcbound (hboundResidue.trans_le hresidueC)
  by_cases hresidueEq : residue = C
  · subst residue
    rw [Nat.mod_eq_of_lt hcC, Nat.mod_self] at hmod
    omega
  · have hresidueLt : residue < C := lt_of_le_of_ne hresidueC hresidueEq
    rw [Nat.mod_eq_of_lt hcC, Nat.mod_eq_of_lt hresidueLt] at hmod
    omega
end ErdosProblems.Erdos269

open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {C bound : ℕ} {x c : ℤ}
    (hC : 0 < C)
    (hcpos : 0 < c)
    (hcbound : Int.natAbs c ≤ bound)
    (hescape : bound < leastPositiveResidue C x)
    (hmod : Int.ModEq C c x) :
    False := by
  have hresidue :=
    leastPositiveResidue_pos_le hC x
  have hmodInt :
      ((Int.natAbs c : ℕ) : ℤ) % (C : ℤ) =
        ((leastPositiveResidue C x : ℕ) : ℤ) % (C : ℤ) := by
    have hcx :
        Int.ModEq C ((Int.natAbs c : ℕ) : ℤ) x := by
      simpa [Int.natAbs_of_nonneg hcpos.le] using hmod
    exact (hcx.trans (leastPositiveResidue_modEq hC x).symm).eq
  have hmodNat :
      Int.natAbs c % C = leastPositiveResidue C x % C := by
    exact_mod_cast hmodInt
  exact no_bounded_positive_state_of_residue_escape
    (Int.natAbs_pos.mpr hcpos.ne')
    hcbound
    ⟨hescape, hresidue.2⟩
    hmodNat
