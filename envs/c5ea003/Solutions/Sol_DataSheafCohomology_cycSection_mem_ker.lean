-- Prove2me | solution 1 for DataSheafCohomology.cycSection_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T17:32:27.917489+00:00
-- url     : https://prove2.me/submissions/c3e33467-f3eb-41ab-bb0f-310b4d513bfe

import Mathlib
import Definitions.Def_Algebra_DataSheafCohomology
open DataSheafCohomology Finset in
theorem solution {K : Type*} [Field K] {m : ℕ} {a : ℕ → K} (ha : ∀ j, j < m + 1 → a j ≠ 0)
    (hh : holonomy a m = 1) :
    ∀ i : Fin (m+1), a i.val * cycSection a m (i + 1) = cycSection a m i := by
  intro i
  simp only [cycSection]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 i.isLt) with hi | hi
  · -- interior step: one more factor `a i` in the transported product
    have hv : ((i + 1 : Fin (m+1)) : ℕ) = i.val + 1 :=
      Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; exact hi)
    rw [hv, prod_range_succ, mul_inv, mul_left_comm, mul_inv_cancel₀ (ha _ (by omega)), mul_one]
  · -- wrap-around step: trivial holonomy closes the loop
    have hil : i = Fin.last m := Fin.ext (by rw [Fin.val_last]; exact hi)
    subst hil
    rw [Fin.last_add_one, Fin.val_zero, prod_range_zero, inv_one, mul_one, Fin.val_last]
    unfold holonomy at hh
    rw [prod_range_succ] at hh
    exact eq_inv_of_mul_eq_one_right hh
