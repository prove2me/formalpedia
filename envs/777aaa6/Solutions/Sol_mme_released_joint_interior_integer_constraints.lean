-- Prove2me | solution 1 for mme_released_joint_interior_integer_constraints
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T09:46:57.786461+00:00
-- url     : https://prove2.me/submissions/eabb5306-efae-4bb3-af3e-e5c1898da844

import Definitions.Def_mme_released_joint_interior_profiles
import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact
import Theorems.Thm_mme_regional_reference_exists_iff_mass

open scoped BigOperators
open MME MME.RecursiveYZ MME.CompleteSplit MME.MoreAsymmetryExactSeed
open MME.ReleasedJointInterior

private theorem reverse_boundary {half R ell : ℕ} {p : Fin R → Fin 3 → ℕ}
    (mu : Fin 3 → Cell half R p → CompleteWord ell → ℕ)
    (hb : BoundaryProfiles mu) (c : Cell half R p)
    (i j z : Fin 3) (hij : i ≠ j) (hiz : i ≠ z) (hjz : j ≠ z)
    (hz : (c.2.val z).val = 0) (w : CompleteWord ell) :
    mu i c w = mu j c (fun h => Fin.rev (w h)) := by
  fin_cases i <;> fin_cases j <;> fin_cases z <;> try contradiction
  all_goals first
    | exact hb.1 c hz w
    | exact hb.2.1 c hz w
    | exact hb.2.2 c hz w
    | simpa using (hb.1 c hz (fun h => Fin.rev (w h))).symm
    | simpa using (hb.2.1 c hz (fun h => Fin.rev (w h))).symm
    | simpa using (hb.2.2 c hz (fun h => Fin.rev (w h))).symm

private theorem split_complement (r : Fin 6) (j : Fin 270)
    (c : RecursiveThinSplit.Split 4 (parent r j)) :
    (splitEquiv r j).symm (complement (parent_total r j) c) =
      complement (ReleasedInterior.parent_total (component j).2 r)
        ((splitEquiv r j).symm c) := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change
    ReleasedInterior.parent (component j).2 0
        (orientation (component j).1 r ((orientation (component j).1 r).symm i)) -
      (c.val ((orientation (component j).1 r).symm i)).val =
    ReleasedInterior.parent (component j).2 r i -
      (c.val ((orientation (component j).1 r).symm i)).val
  simp only [Equiv.apply_symm_apply]
  rfl

-- The constructor-name linter unfolds the concrete histogram tables past its recursion limit.
set_option linter.constructorNameAsVariable false in
/-- Every joint inner region has exact split and child masses, supported grades,
CW boundary symmetry, and a common divisible scale. The region includes all six
outer owners and all parent shapes; zero-weight labels require no extraction. -/
theorem solution
    (r : Fin 6) (k : ℕ) (hk : 0 < k) :
    ∃ reference : RecursiveXHash.Address 4 270 (parent r) (size r k),
      reference ∈ RecursiveXHash.target (n := size r k) (splitCount r k) ∧
      (∀ i c, ∑ w, integerProfile r k i c w =
        splitCount r k c.1 c.2 +
          splitCount r k c.1 (complement (parent_total r c.1) c.2)) ∧
      (∀ i c w, 0 < integerProfile r k i c w →
        ∑ h, (w h).val = (c.2.val i).val) ∧
      BoundaryProfiles (integerProfile r k) ∧
      (∀ j, size r k j ≠ 0 → k * denominator ^ 2 ≤ size r k j) ∧
      (∀ j c, k * denominator ^ 2 ∣ splitCount r k j c) := by
  classical
  have hinterior (j : Fin 270) (hw : weight j ≠ 0) :
      (ReleasedInterior.seed (component j).1 (component j).2).boundary = [] := by
    by_contra h
    simp only [weight, if_neg h] at hw
    exact hw rfl
  have source (j : Fin 270) (hw : 0 < weight j) :=
    mme_released_interior_scaled_integer_profile_constraints_exact
      (component j).1 (component j).2 (hinterior j hw.ne')
      (k * weight j) (Nat.mul_pos hk hw)
  have hcounts (j : Fin 270) :
      ∑ c, splitCount r k j c = size r k j := by
    by_cases hw : weight j = 0
    · simp [splitCount, size, hw]
    · obtain ⟨a, ha, _⟩ := source j (Nat.pos_of_ne_zero hw)
      have hc := (mme_regional_reference_exists_iff_mass
        (fun s c => k * weight j * ReleasedInterior.splitCount
          (component j).1 (component j).2 s c)).mp ⟨a, ha⟩ r
      change (∑ c, k * weight j * ReleasedInterior.splitCount
        (component j).1 (component j).2 r ((splitEquiv r j).symm c)) = _
      exact (Equiv.sum_comp (splitEquiv r j).symm
        (fun c => k * weight j *
          ReleasedInterior.splitCount (component j).1 (component j).2 r c)).trans hc
  obtain ⟨reference, href⟩ :=
    (mme_regional_reference_exists_iff_mass (half := 4) (R := 270)
      (parent := parent r) (n := size r k) (splitCount r k)).mpr hcounts
  refine ⟨reference, ?_⟩
  constructor
  · assumption
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i c
    by_cases hw : weight c.1 = 0
    · simp [integerProfile, splitCount, hw]
    · obtain ⟨_, _, _, hm, _⟩ := source c.1 (Nat.pos_of_ne_zero hw)
      simpa only [integerProfile, splitCount, split_complement] using
        hm (orientation (component c.1).1 r i) ⟨r, (splitEquiv r c.1).symm c.2⟩
  · intro i c w hw
    have hweight : weight c.1 ≠ 0 := by
      intro h
      simp [integerProfile, h] at hw
    obtain ⟨_, _, _, _, hs, _⟩ := source c.1 (Nat.pos_of_ne_zero hweight)
    have h := hs (orientation (component c.1).1 r i)
      ⟨r, (splitEquiv r c.1).symm c.2⟩ w hw
    change (∑ h, (w h).val) =
      (c.2.val ((orientation (component c.1).1 r).symm
        (orientation (component c.1).1 r i))).val at h
    simpa only [Equiv.symm_apply_apply] using h
  · have hb (j : Fin 270) :
        BoundaryProfiles (fun i c w => k * weight j *
          ReleasedInterior.integerProfile (component j).1 (component j).2 i c w) := by
      by_cases hw : weight j = 0
      · simp [BoundaryProfiles, hw]
      · obtain ⟨_, _, _, _, _, hb, _⟩ := source j (Nat.pos_of_ne_zero hw)
        exact hb
    have hpair (c : Cell 4 270 (parent r)) (i j z : Fin 3)
        (hij : i ≠ j) (hiz : i ≠ z) (hjz : j ≠ z)
        (hz : (c.2.val z).val = 0) (w : CompleteWord 2) :
        integerProfile r k i c w =
          integerProfile r k j c (fun h => Fin.rev (w h)) := by
      apply reverse_boundary _ (hb c.1) ⟨r, (splitEquiv r c.1).symm c.2⟩
        (orientation (component c.1).1 r i) (orientation (component c.1).1 r j)
        (orientation (component c.1).1 r z)
        ((orientation (component c.1).1 r).injective.ne hij)
        ((orientation (component c.1).1 r).injective.ne hiz)
        ((orientation (component c.1).1 r).injective.ne hjz)
      change (c.2.val ((orientation (component c.1).1 r).symm
        (orientation (component c.1).1 r z))).val = 0
      simpa only [Equiv.symm_apply_apply] using hz
    exact ⟨fun c hz w => hpair c 1 0 2 (by decide) (by decide) (by decide) hz w,
      fun c hz w => hpair c 2 1 0 (by decide) (by decide) (by decide) hz w,
      fun c hz w => hpair c 2 0 1 (by decide) (by decide) (by decide) hz w⟩
  · intro j hj
    have hw : weight j ≠ 0 := by
      intro h
      simp [size, h] at hj
    obtain ⟨_, _, _, _, _, _, _, hsize, _⟩ := source j (Nat.pos_of_ne_zero hw)
    have hscale : k * denominator ^ 2 ≤ k * weight j * denominator ^ 2 := by
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hw))
    exact hscale.trans (hsize r hj)
  · intro j c
    by_cases hw : weight j = 0
    · simp [splitCount, hw]
    · obtain ⟨_, _, _, _, _, _, _, _, hdiv⟩ := source j (Nat.pos_of_ne_zero hw)
      have hd : k * denominator ^ 2 ∣ k * weight j * denominator ^ 2 := by
        exact ⟨weight j, by ring⟩
      exact hd.trans (hdiv r ((splitEquiv r j).symm c))


#print axioms solution
