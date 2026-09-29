-- Prove2me | solution 1 for mme_common_hash_scale_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T14:25:48.832377+00:00
-- url     : https://prove2.me/submissions/d6fb2e2c-0451-49d6-80d9-5a4bf43ccd0d

import Definitions.Def_mme_recursive_region_hash_loads
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false

/-- Multiplying all load numerators by at most d multiplies the common hash
scale by at most d; the quotient rounding is absorbed into its existing slack. -/
theorem solution {J : Type*} [Fintype J]
    (grade d : ℕ) (hd : 1 ≤ d) (num num' den : J → ℕ)
    (hnum : ∀ j, num' j ≤ d * num j) :
    commonScale grade num' den ≤ d * commonScale grade num den := by
  classical
  have hquot (j : J) : num' j / den j + 1 ≤ d * (num j / den j + 1) := by
    by_cases hz : den j = 0
    · simp [hz, hd]
    · have hden : 0 < den j := Nat.pos_of_ne_zero hz
      have hrem := Nat.mod_lt (num j) hden
      have hdecomp := Nat.mod_add_div (num j) (den j)
      have hbase : num j < den j * (num j / den j + 1) := by nlinarith
      have hmul := Nat.mul_lt_mul_of_pos_left hbase (lt_of_lt_of_le Nat.zero_lt_one hd)
      have hlt : num' j < d * (num j / den j + 1) * den j := by
        nlinarith [hnum j]
      have hdiv := (Nat.div_lt_iff_lt_mul hden).mpr hlt
      omega
  unfold commonScale
  apply max_le
  · exact (le_max_left _ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  · apply Finset.sup_le
    intro j hj
    exact (hquot j).trans (Nat.mul_le_mul_left d
      ((Finset.le_sup (f := fun j => num j / den j + 1) hj).trans (le_max_right _ _)))

/-- Changing the repair scale affects regional hash loads by at most that
same factor, including the ambient load that is independent of repair. -/
private theorem mme_regional_hash_scale_le_repair_mul
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (mu : Fin 2 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (keep : Fin 2 → Address half R parent n →
      (Position n → CompleteSplit.CompleteWord ell) → Prop) :
    commonScale half (loadNum htotal m d mu keep) (loadDen m) ≤
      d * commonScale half (loadNum htotal m 1 mu keep) (loadDen m) := by
  apply solution half d hd
  intro j
  rcases j with u | ⟨i, a, f⟩
  · dsimp [loadNum]
    exact Nat.le_mul_of_pos_left _ (by omega)
  · dsimp [loadNum]
    split
    · exact le_of_eq (by ring)
    · simp

/-- A fixed repair scale contributes only log d to the hash log-scale. -/
private theorem mme_regional_hash_log_scale_le_repair_log
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (mu : Fin 2 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (keep : Fin 2 → Address half R parent n →
      (Position n → CompleteSplit.CompleteWord ell) → Prop) :
    Real.log (commonScale half (loadNum htotal m d mu keep) (loadDen m)) ≤
      Real.log d + Real.log (commonScale half (loadNum htotal m 1 mu keep) (loadDen m)) := by
  have hpos (s : ℕ) : 0 < commonScale half (loadNum htotal m s mu keep) (loadDen m) :=
    lt_of_lt_of_le (Nat.zero_lt_succ half) (le_max_left _ _)
  have hbound := mme_regional_hash_scale_le_repair_mul htotal m d hd mu keep
  have hcast : (commonScale half (loadNum htotal m d mu keep) (loadDen m) : ℝ) ≤
      (d : ℝ) * (commonScale half (loadNum htotal m 1 mu keep) (loadDen m) : ℝ) := by
    exact_mod_cast hbound
  have hlog := Real.log_le_log (by exact_mod_cast hpos d) hcast
  rw [Real.log_mul (by exact_mod_cast (show d ≠ 0 by omega))
    (by exact_mod_cast (hpos 1).ne')] at hlog
  exact hlog


#print axioms solution
