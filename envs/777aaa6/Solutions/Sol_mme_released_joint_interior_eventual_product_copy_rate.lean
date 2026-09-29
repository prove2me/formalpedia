-- Prove2me | solution 1 for mme_released_joint_interior_eventual_product_copy_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:36:54.490782+00:00
-- url     : https://prove2.me/submissions/24d7fb13-dd48-48e6-a522-ebfdadce3e30

import Theorems.Thm_mme_released_joint_interior_eventual_positive_copy_rate

open scoped BigOperators
open MME MME.ReleasedJointInterior MME.RecursiveYZ MME.RegionRealization
open MME.ProfiledCW MME.CompleteSplit MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells MME.RegionRate Filter

-- The name linter unfolds the concrete released histogram tables.
set_option linter.constructorNameAsVariable false in
/-- Positive pooled rates produce all six joint exact outputs simultaneously.
The product of their actual repaired multiplicities retains the sum of the
regional entropy rates with all window, repair and asymptotic losses. -/
theorem solution
    (eta : ℝ) (heta : 0 < eta) (loss : ℝ) (hloss : 0 < loss)
    (eps : ℝ) (heps : 0 < eps) :
    let rate : Fin 6 → ℝ := fun r =>
      regionalRate (parent_total r) (size r 1) (splitCount r 1) (integerProfile r 1) -
        (blocks r 1 : ℝ) * entropyModulus (Fin 2 → CompleteWord 2) eps -
        4 * eta * (blocks r 1 : ℝ) - loss
    (∀ r, 0 < rate r) → ∀ᶠ k : ℕ in atTop,
      ∃ (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
        (E : ∀ r : Fin 6, ExactStep 2 (blocks r k * 4) (gradedSource r k eps)),
        (∀ r, a r ∈ RecursiveXHash.target (n := size r k) (splitCount r k)) ∧
        (∀ r, (E r).output = fun i x =>
          Graded (parent_total r) i (a r)
            (ProfiledCW.split (positions r k) (positions_length r k) x) ∧
          Useful (fullCell (parent_total r) (a r)) (integerProfile r k i)
            (ProfiledCW.split (positions r k) (positions_length r k) x)) ∧
        (∀ r, 0 < (E r).copies) ∧
        0 < ∏ r, (E r).copies ∧
        Real.exp ((∑ r, rate r) * (k : ℝ)) ≤ (∏ r, (E r).copies : ℕ) := by
  classical
  intro rate hpositive
  obtain ⟨d, hd, hsteps⟩ :=
    mme_released_joint_interior_eventual_positive_copy_rate eta heta loss hloss eps heps
  filter_upwards [hsteps] with k hk
  choose a ha hrest using fun r => hk r (hpositive r)
  choose E hcount hexponent houtput hrepair hpos hlog using hrest
  refine ⟨a, E, ?_, houtput, hpos, Finset.prod_pos (fun r _ => hpos r), ?_⟩
  · unfold RecursiveXHash.target at ha ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  have hcomponent (r : Fin 6) : Real.exp (rate r * (k : ℝ)) ≤ (E r).copies := by
    have h := Real.exp_le_exp.mpr (hlog r).le
    rwa [Real.exp_log (Nat.cast_pos.mpr (hpos r))] at h
  calc
    Real.exp ((∑ r, rate r) * (k : ℝ)) = ∏ r, Real.exp (rate r * (k : ℝ)) := by
      rw [Finset.sum_mul, Real.exp_sum]
    _ ≤ ∏ r, ((E r).copies : ℝ) :=
      Finset.prod_le_prod (fun r _ => (Real.exp_pos _).le) (fun r _ => hcomponent r)
    _ = (∏ r, (E r).copies : ℕ) := by rw [Nat.cast_prod]


#print axioms solution
