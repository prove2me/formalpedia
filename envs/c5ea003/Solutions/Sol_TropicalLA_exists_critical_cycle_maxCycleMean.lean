-- Prove2me | solution 1 for TropicalLA.exists_critical_cycle_maxCycleMean
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T08:06:12.602136+00:00
-- url     : https://prove2.me/submissions/6bfc7e03-730a-4b68-a24e-8faac3a4ee2c

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ} :
    ∃ (m : ℕ) (c : ℕ → ι), 0 < m ∧ m ≤ Fintype.card ι ∧ c m = c 0 ∧
      pathWeight A c m = m * maxCycleMean A := by
  classical
  have hstep : ∀ m i t, tpow A (m + 1) i t
      = univ.sup' univ_nonempty (fun l => tpow A m i l + A l t) := fun _ _ _ => rfl
  -- optimal walks are attained
  have hattain : ∀ m i t, ∃ p : ℕ → ι, p 0 = i ∧ p (m + 1) = t ∧
      pathWeight A p (m + 1) = tpow A m i t := by
    intro m
    induction m with
    | zero =>
      intro i t
      refine ⟨fun s => if s = 0 then i else t, by simp, by simp, ?_⟩
      simp [pathWeight, tpow]
    | succ m ih =>
      intro i t
      obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' univ_nonempty
        (fun l => tpow A m i l + A l t)
      obtain ⟨p, hp0, hpm, hpw⟩ := ih i l
      refine ⟨fun s => if s ≤ m + 1 then p s else t, by simp [hp0], by simp, ?_⟩
      have e1 : pathWeight A (fun s => if s ≤ m + 1 then p s else t) (m + 1)
          = pathWeight A p (m + 1) := by
        unfold pathWeight
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs' := Finset.mem_range.1 hs
        simp only [show s ≤ m + 1 by omega, show s + 1 ≤ m + 1 by omega, if_true]
      have e2 : pathWeight A (fun s => if s ≤ m + 1 then p s else t) (m + 1 + 1)
          = pathWeight A (fun s => if s ≤ m + 1 then p s else t) (m + 1) + A l t := by
        unfold pathWeight
        rw [Finset.sum_range_succ]
        simp only [le_refl, if_true, show ¬ (m + 1 + 1 ≤ m + 1) by omega, if_false, hpm]
      rw [e2, e1, hpw, hstep m i t, hl]
  -- a maximising index for the cycle mean
  obtain ⟨⟨k, i⟩, hki, hmu⟩ := Finset.exists_mem_eq_sup' (cycleIndex_nonempty (ι := ι))
    (fun q : ℕ × ι => tpow A q.1 q.2 q.2 / ((q.1 : ℝ) + 1))
  have hmu' : maxCycleMean A = tpow A k i i / ((k : ℝ) + 1) := hmu
  have hk : k < Fintype.card ι := Finset.mem_range.1 (Finset.mem_product.1 hki).1
  obtain ⟨p, hp0, hpk, hpw⟩ := hattain k i i
  refine ⟨k + 1, p, by omega, by omega, by rw [hpk, hp0], ?_⟩
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [hpw, hmu']
  push_cast
  field_simp
