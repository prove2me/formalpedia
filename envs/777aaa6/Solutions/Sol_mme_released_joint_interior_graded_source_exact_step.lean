-- Prove2me | solution 1 for mme_released_joint_interior_graded_source_exact_step
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:08:07.905078+00:00
-- url     : https://prove2.me/submissions/e42c4b27-8cea-43fe-812a-e764cdc5ee04

import Definitions.Def_mme_released_joint_interior_graded_source
import Theorems.Thm_mme_released_joint_interior_integer_constraints
import Theorems.Thm_mme_released_joint_interior_positive_blocks
import Theorems.Thm_mme_recursive_region_graded_source_exact_step_allow_empty

open scoped BigOperators
open MME MME.ReleasedJointInterior MME.RecursiveYZ MME.RegionRealization
open MME.ProfiledCW MME.CompleteSplit MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells

private theorem split_flatten {S : Type} {ell L M : ℕ} (e : Fin L ≃ S)
    (length : L * 2 ^ (ell - 1) = M) (f : S → CompleteWord ell) :
    ProfiledCW.split e length (ProfiledCW.flatten e length f) = f := by
  funext p h
  simp [ProfiledCW.split, ProfiledCW.flatten]

-- The name linter unfolds the concrete histogram tables past its recursion limit.
set_option linter.constructorNameAsVariable false in
/-- One hashing step acts jointly on every released owner and parent shape in
inner region `r`. Its graded source retains every prescribed target address.
The original hashing copy bound and explicit repair exponent are unchanged. -/
theorem solution
    (r : Fin 6) (k : ℕ) (hk : 0 < k) (d : ℕ) (hd : 1 < d)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * 270 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2) ≤
      (k * denominator ^ 2 : ℕ) * eps ^ 2) :
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
        E.output = fun i x =>
          Graded (parent_total r) i reference
            (ProfiledCW.split (positions r k) (positions_length r k) x) ∧
          Useful (fullCell (parent_total r) reference) (integerProfile r k i)
            (ProfiledCW.split (positions r k) (positions_length r k) x) := by
  classical
  dsimp only
  obtain ⟨reference, href, hmass, hsupport, hboundary, hsize, hdiv⟩ :=
    mme_released_joint_interior_integer_constraints r k hk
  have hpositive := mme_released_joint_interior_positive_blocks r k hk
  have hcard : Fintype.card (Σ j : Fin 270, Fin (size r k j)) = blocks r k := by
    simp only [Fintype.card_sigma, Fintype.card_fin, blocks]
  let e : Fin ((blocks r k - 1) + 1) ≃ (Σ j : Fin 270, Fin (size r k j)) :=
    (finCongr (Nat.sub_add_cancel hpositive)).trans (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨reference, ?_, ?_⟩
  · clear e hcard hpositive hdiv hsize hboundary hsupport hmass
    assumption
  apply mme_recursive_region_graded_source_exact_step_allow_empty
    (parent r) (size r k) (parent_total r) (by decide) (splitCount r k)
    e (positions r k) (positions_length r k) (integerProfile r k)
    hmass hsupport hboundary reference (by
      clear e hcard hpositive hdiv hsize hboundary hsupport hmass
      assumption)
    (k * denominator ^ 2) d (Nat.mul_pos hk (by norm_num [denominator]))
    hd hsize hdiv eps heps hscale (gradedSource r k eps)
  intro i a ha f hg ht
  change source r k eps i _ ∧ ∃ a',
    a' ∈ RecursiveXHash.target (n := size r k) (splitCount r k) ∧
      Graded (parent_total r) i a'
        (ProfiledCW.split (positions r k) (positions_length r k)
          (ProfiledCW.flatten (positions r k) (positions_length r k) f))
  constructor
  · change parentTypical (parent_total r) (size r k) (splitCount r k)
      (integerProfile r k i) eps
      (ProfiledCW.split (positions r k) (positions_length r k)
        (ProfiledCW.flatten (positions r k) (positions_length r k) f))
    rw [split_flatten]
    exact ht
  · refine ⟨a, ?_, ?_⟩
    · generalize htarget : RecursiveXHash.target (n := size r k) (splitCount r k) = T at ha ⊢
      exact ha
    · rw [split_flatten]
      exact hg


#print axioms solution
