-- Prove2me | solution 1 for mme_released_joint_interior_eventual_positive_copy_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:12:56.201509+00:00
-- url     : https://prove2.me/submissions/03a04d5b-f871-4a86-9bba-452a5ab32a3b

import Theorems.Thm_mme_released_joint_interior_eventual_entropy_copy_rate

open scoped BigOperators
open MME MME.ReleasedJointInterior MME.RecursiveYZ MME.RegionRealization
open MME.ProfiledCW MME.CompleteSplit MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells MME.RegionRate Filter

-- The name linter unfolds the concrete released histogram tables.
set_option linter.constructorNameAsVariable false in
/-- Every joint region with positive entropy surplus has positive repaired
multiplicity. The logarithm of the actual count retains its pooled regional
rate, with the prescribed window, repair and asymptotic losses. -/
theorem solution
    (eta : ℝ) (heta : 0 < eta) (loss : ℝ) (hloss : 0 < loss)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ d : ℕ, 1 < d ∧ ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      0 < (regionalRate (parent_total r) (size r 1) (splitCount r 1)
          (integerProfile r 1) - (blocks r 1 : ℝ) *
          entropyModulus (Fin 2 → CompleteWord 2) eps -
          4 * eta * (blocks r 1 : ℝ) - loss) →
    let keep := fun (i : Fin 2)
      (_ : RecursiveXHash.Address 4 270 (parent r) (size r k)) =>
        parentTypical (parent_total r) (size r k) (splitCount r k)
          (integerProfile r k (yzMode i)) eps
    let Q := commonScale 4
      (loadNum (parent_total r) (splitCount r k) d
        (fun i => integerProfile r k (yzMode i)) keep) (loadDen (splitCount r k))
    ∃ reference : RecursiveXHash.Address 4 270 (parent r) (size r k),
      reference ∈ RecursiveXHash.target (n := size r k) (splitCount r k) ∧
      ∃ E : ExactStep 2 (blocks r k * 4) (gradedSource r k eps),
        ((RecursiveXHash.target (n := size r k) (splitCount r k)).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell (parent_total r) reference)
            (fun c i => (c.2.val i).val) (integerProfile r k) i)) + 1 ∧
        (E.output = fun i x =>
          Graded (parent_total r) i reference
            (ProfiledCW.split (positions r k) (positions_length r k) x) ∧
          Useful (fullCell (parent_total r) reference) (integerProfile r k i)
            (ProfiledCW.split (positions r k) (positions_length r k) x)) ∧
        Real.log ((8 : ℝ) ^ E.stage.repairExponent) ≤
          Real.log 8 + eta * (blocks r k * 4 : ℕ) ∧
        0 < E.copies ∧
        (regionalRate (parent_total r) (size r 1) (splitCount r 1)
          (integerProfile r 1) - (blocks r 1 : ℝ) *
          entropyModulus (Fin 2 → CompleteWord 2) eps -
          4 * eta * (blocks r 1 : ℝ) - loss) * (k : ℝ) < Real.log E.copies := by
  classical
  obtain ⟨d, hd, hsteps⟩ :=
    mme_released_joint_interior_eventual_entropy_copy_rate eta heta
      (loss / 2) (by positivity) eps heps
  refine ⟨d, hd, ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.log 2 / (loss / 2))
  filter_upwards [hsteps, eventually_ge_atTop (N + 1)] with k hk hkN
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hNk : (N : ℝ) < k := by exact_mod_cast (show N < k by omega)
  have hlarge : Real.log 2 < (loss / 2) * (k : ℝ) := by
    have h := (div_lt_iff₀ (show 0 < loss / 2 by positivity)).mp (hN.trans hNk)
    simpa only [mul_comm] using h
  intro r hrate
  obtain ⟨reference, href, E, hcount, hexponent, houtput, hrepair, hlog⟩ := hk r
  refine ⟨reference, ?_, E, hcount, hexponent, houtput, hrepair, ?_⟩
  · unfold RecursiveXHash.target at href ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at href ⊢
    exact href
  · let rate : ℝ := regionalRate (parent_total r) (size r 1) (splitCount r 1)
          (integerProfile r 1) - (blocks r 1 : ℝ) *
          entropyModulus (Fin 2 → CompleteWord 2) eps -
          4 * eta * (blocks r 1 : ℝ) - loss
    have hratepos : 0 < rate := hrate
    have hlog' : (rate + loss / 2) * (k : ℝ) < Real.log (E.copies + 1 : ℕ) := by
      have heq (x : ℝ) : (x - loss + loss / 2) * (k : ℝ) =
          (x - loss / 2) * (k : ℝ) := by ring
      exact (heq _).trans_lt hlog
    have hcopies : 0 < E.copies := by
      by_contra h
      have hz : E.copies = 0 := by omega
      rw [hz] at hlog'
      norm_num at hlog'
      have := mul_pos (show 0 < rate + loss / 2 by positivity) hkR
      linarith
    refine ⟨hcopies, ?_⟩
    have hc : (0 : ℝ) < E.copies := Nat.cast_pos.mpr hcopies
    have hround : Real.log (E.copies + 1 : ℕ) ≤ Real.log 2 + Real.log E.copies := by
      have hle : ((E.copies + 1 : ℕ) : ℝ) ≤ 2 * (E.copies : ℝ) := by
        exact_mod_cast (show E.copies + 1 ≤ 2 * E.copies by omega)
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (E.copies + 1 : ℕ)) hle
      rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hc.ne'] at h
    change rate * (k : ℝ) < _
    nlinarith only [hlog', hround, hlarge]


#print axioms solution
