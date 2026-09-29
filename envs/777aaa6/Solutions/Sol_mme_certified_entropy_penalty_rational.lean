-- Prove2me | solution 1 for mme_certified_entropy_penalty_rational
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T01:41:42.82298+00:00
-- url     : https://prove2.me/submissions/e1245898-e032-4cb1-ad9f-286eaeab9941

import Mathlib
import Definitions.Def_mme_certified_entropy_reference
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_certified_entropy_bounds
import Theorems.Thm_mme_certified_entropy_penalty

open BigOperators MME MME.RegionRate MME.RecursiveThinSplit MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000


namespace MME.Cert

variable {half : ℕ} {parent : Fin 3 → ℕ}

/-- Exponent vectors add under the reference value. -/
theorem qval_sum3' (E : Fin 3 → (Fin 4 → ℤ)) :
    qval (fun k ↦ ∑ i, E i k) = ∏ i, qval (E i) := by
  simp only [qval, Fin.sum_univ_three, Fin.prod_univ_three]
  rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (3:ℝ) ≠ 0), zpow_add₀ (by norm_num : (3:ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (5:ℝ) ≠ 0), zpow_add₀ (by norm_num : (5:ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (7:ℝ) ≠ 0), zpow_add₀ (by norm_num : (7:ℝ) ≠ 0)]
  ring

theorem log_qval_sum3 (E : Fin 3 → (Fin 4 → ℤ)) :
    Real.log (qval (fun k ↦ ∑ i, E i k)) = ∑ i, Real.log (qval (E i)) := by
  rw [qval_sum3' E, Fin.prod_univ_three, Fin.sum_univ_three,
    Real.log_mul (mul_pos (qval_pos _) (qval_pos _)).ne' (qval_pos _).ne',
    Real.log_mul (qval_pos _).ne' (qval_pos _).ne']

/-- The entropy penalty is bounded by a purely rational expression: the logarithms in the Gibbs
dual bound cancel against those in the Gibbs entropy bound. -/
theorem penalty_rational (alpha : RecursiveThinSplit.Split half parent → ℚ)
    (hp : ∀ c, 0 ≤ alpha c) (hm : ∑ c, alpha c = 1)
    (E : Fin 3 → Fin (half + 1) → (Fin 4 → ℤ)) :
    Real.log 2 * entropyPenalty (fun c ↦ ((alpha c : ℚ) : ℝ)) ≤
      (((∑ c : RecursiveThinSplit.Split half parent,
          qvalQ (fun k ↦ ∑ i, E i (c.val i) k)) - 2 +
        ∑ c : RecursiveThinSplit.Split half parent,
          (alpha c) ^ 2 / qvalQ (fun k ↦ ∑ i, E i (c.val i) k) : ℚ) : ℝ) := by
  classical
  set e : RecursiveThinSplit.Split half parent → Fin 4 → ℤ :=
    fun c k ↦ ∑ i, E i (c.val i) k with he
  have hmr : ∑ c, ((alpha c : ℚ) : ℝ) = 1 := by
    rw [← Rat.cast_sum, hm]
    norm_num
  -- the Gibbs dual bound
  have hdual := mme_certified_entropy_penalty.2 (fun c ↦ ((alpha c : ℚ) : ℝ))
    (fun c ↦ by show (0:ℝ) ≤ ((alpha c : ℚ) : ℝ); exact_mod_cast hp c) hmr E
  -- the Gibbs entropy bound with the same reference
  have hent := mme_certified_entropy_bounds.1 (fun c ↦ ((alpha c : ℚ) : ℝ))
    (fun c ↦ by show (0:ℝ) ≤ ((alpha c : ℚ) : ℝ); exact_mod_cast hp c) e
  -- the cross terms agree
  have hcross : ∀ c : RecursiveThinSplit.Split half parent,
      Real.log (qval (e c)) = ∑ i, Real.log (qval (E i (c.val i))) := by
    intro c
    exact log_qval_sum3 (fun i ↦ E i (c.val i))
  have hsplit : ∑ c : RecursiveThinSplit.Split half parent,
      (((alpha c : ℚ) : ℝ) - ((alpha c : ℚ) : ℝ) ^ 2 / qval (e c) -
        ((alpha c : ℚ) : ℝ) * Real.log (qval (e c))) =
      1 - (∑ c, ((alpha c : ℚ) : ℝ) ^ 2 / qval (e c)) -
        ∑ c, ((alpha c : ℚ) : ℝ) * ∑ i, Real.log (qval (E i (c.val i))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hmr]
    congr 1
    exact Finset.sum_congr rfl (fun c _ ↦ by rw [hcross c])
  rw [hsplit] at hent
  -- log Z ≤ Z - 1
  have hZpos : (0 : ℝ) < ∑ c : RecursiveThinSplit.Split half parent,
      qval (fun k ↦ ∑ i, E i (c.val i) k) := by
    have hne : Nonempty (RecursiveThinSplit.Split half parent) := by
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hm
      exact absurd hm (by norm_num)
    haveI := hne
    exact Finset.sum_pos (fun c _ ↦ qval_pos _) Finset.univ_nonempty
  have hlogZ := Real.log_le_sub_one_of_pos hZpos
  have hq : ∀ c : RecursiveThinSplit.Split half parent,
      ((qvalQ (fun k ↦ ∑ i, E i (c.val i) k) : ℚ) : ℝ) = qval (e c) := fun c ↦ qvalQ_cast _
  push_cast
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ hq c),
    Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) ↦ by rw [hq c] :
      ∀ c ∈ Finset.univ, ((alpha c : ℚ) : ℝ) ^ 2 /
        ((qvalQ (fun k ↦ ∑ i, E i (c.val i) k) : ℚ) : ℝ) =
        ((alpha c : ℚ) : ℝ) ^ 2 / qval (e c))]
  linarith [hdual, hent, hlogZ]


end MME.Cert

theorem solution :
    ∀ {half : ℕ} {parent : Fin 3 → ℕ} (alpha : RecursiveThinSplit.Split half parent → ℚ),
      (∀ c, 0 ≤ alpha c) → ∑ c, alpha c = 1 →
      ∀ E : Fin 3 → Fin (half + 1) → (Fin 4 → ℤ),
      Real.log 2 * entropyPenalty (fun c ↦ ((alpha c : ℚ) : ℝ)) ≤
        (((∑ c : RecursiveThinSplit.Split half parent,
            qvalQ (fun k ↦ ∑ i, E i (c.val i) k)) - 2 +
          ∑ c : RecursiveThinSplit.Split half parent,
            (alpha c) ^ 2 / qvalQ (fun k ↦ ∑ i, E i (c.val i) k) : ℚ) : ℝ) :=
  fun {half} {parent} alpha hp hm E ↦ MME.Cert.penalty_rational alpha hp hm E
