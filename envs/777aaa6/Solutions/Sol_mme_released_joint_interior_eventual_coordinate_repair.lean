-- Prove2me | solution 1 for mme_released_joint_interior_eventual_coordinate_repair
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:39:42.224444+00:00
-- url     : https://prove2.me/submissions/41d9776d-310c-41f0-8ebc-a2833b8cc11a

import Theorems.Thm_mme_released_joint_interior_graded_source_exact_step
import Theorems.Thm_mme_profile_repair_scale_exists_uniform_coordinate_loss

open scoped BigOperators
open MME MME.ReleasedJointInterior MME.RecursiveYZ MME.RegionRealization
open MME.ProfiledCW MME.CompleteSplit MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells Filter

-- The name linter unfolds the concrete released histogram tables.
set_option linter.constructorNameAsVariable false in
/-- All six joint regions admit their exact graded extraction at every large
enough scale. One repair base makes the logarithmic cost arbitrarily small per
physical coordinate, uniformly over all 270 labels in each region. -/
theorem solution
    (eta : ℝ) (heta : 0 < eta) (eps : ℝ) (heps : 0 < eps) :
    ∃ d : ℕ, 1 < d ∧ ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
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
          Real.log 8 + eta * (blocks r k * 4 : ℕ) := by
  classical
  obtain ⟨d, hd, hrepair⟩ :=
    mme_profile_repair_scale_exists_uniform_coordinate_loss eta heta
  refine ⟨d, hd, ?_⟩
  let B : ℝ := (8 * d : ℝ) *
    (25 * 270 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2)
  have hfactor : 0 < (denominator : ℝ) ^ 2 * eps ^ 2 :=
    mul_pos (by norm_num [denominator]) (sq_pos_of_pos heps)
  obtain ⟨j, hj⟩ := exists_nat_gt (B / ((denominator : ℝ) ^ 2 * eps ^ 2))
  apply eventually_atTop.mpr
  refine ⟨j + 1, fun k hk r => ?_⟩
  have hkpos : 0 < k := by omega
  have hjk : (j : ℝ) < k := by exact_mod_cast (show j < k by omega)
  have hB := (div_lt_iff₀ hfactor).mp (hj.trans hjk)
  have hscale : (8 * d : ℝ) *
      (25 * 270 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2) ≤
      (k * denominator ^ 2 : ℕ) * eps ^ 2 := by
    simpa only [B, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hB.le
  obtain ⟨reference, href, E, hcount, hexponent, houtput⟩ :=
    mme_released_joint_interior_graded_source_exact_step r k hkpos d hd eps heps hscale
  refine ⟨reference, ?_, E, hcount, hexponent, houtput, ?_⟩
  · unfold RecursiveXHash.target at href ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at href ⊢
    exact href
  · rw [hexponent]
    have hlength : Fintype.card (Position (size r k)) * 2 ^ (2 - 1) =
        blocks r k * 4 := by
      simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
        ← Finset.sum_mul, blocks]
      omega
    have h := hrepair 2 (Position (size r k)) (Cell 4 270 (parent r))
      (fullCell (parent_total r) reference) (fun c i => (c.2.val i).val)
      (integerProfile r k)
    simpa only [hlength] using h


#print axioms solution
