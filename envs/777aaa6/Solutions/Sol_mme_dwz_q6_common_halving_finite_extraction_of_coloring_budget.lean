-- Prove2me | solution 1 for mme_dwz_q6_common_halving_finite_extraction_of_coloring_budget
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:49:06.255662+00:00
-- url     : https://prove2.me/submissions/34a89fde-c86f-48a5-9d96-6874167506c7

import Theorems.Thm_mme_dwz_q6_paired_coloring_six_symmetrized_matrix_extraction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MME MME.DWZComponentRestriction BigOperators
universe u
set_option autoImplicit false

/-- A sufficiently economical paired coloring supplies the full prescribed
finite-extraction inequality from the literal restricted source. -/
theorem solution
    {K : Type u} [Field K] (tau : ℝ)
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m L G A H : ℕ) {k : ℕ}
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving) (hk : 0 < k)
    (coloring : (family.pairedCyclicConflictGraph halving).Coloring (Fin k))
    (hbudget : (k : ℝ) ^ 3 * Real.exp (-200 * Real.sqrt
      (((DWZTable2Counts.component s * m + 1 : ℕ) : ℝ))) ≤ H) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (restrictedComponentPower K s m)) ∧
      (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau) *
          Real.exp (-200 * Real.sqrt
            (((DWZTable2Counts.component s * m + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨q, a, b, c, hcount, hrestrict, hvol⟩ :=
    mme_dwz_q6_paired_coloring_six_symmetrized_matrix_extraction
      (K := K) s hs m L G A H family halving hk coloring
  refine ⟨q, a, b, c, hrestrict, ?_⟩
  let loss := Real.exp (-200 * Real.sqrt
    (((DWZTable2Counts.component s * m + 1 : ℕ) : ℝ)))
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hcountreal : (A : ℝ) ^ 3 * (H : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 * q := by
    exact_mod_cast hcount
  have hweight : (A : ℝ) ^ 3 * (H : ℝ) ^ 2 * loss ≤ q := by
    apply (mul_le_mul_iff_right₀ (pow_pos hkreal 3)).mp
    calc
      (k : ℝ) ^ 3 * ((A : ℝ) ^ 3 * (H : ℝ) ^ 2 * loss) =
          ((A : ℝ) ^ 3 * (H : ℝ) ^ 2) * ((k : ℝ) ^ 3 * loss) := by ring
      _ ≤ ((A : ℝ) ^ 3 * (H : ℝ) ^ 2) * H :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = (A : ℝ) ^ 3 * (H : ℝ) ^ 3 := by ring
      _ ≤ (k : ℝ) ^ 3 * q := hcountreal
  have hweighted := mul_le_mul_of_nonneg_right hweight
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ)) tau)
  simp only [hvol, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow]
  simpa only [loss, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hweighted
