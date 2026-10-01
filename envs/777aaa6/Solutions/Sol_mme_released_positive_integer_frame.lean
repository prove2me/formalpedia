-- Prove2me | solution 1 for mme_released_positive_integer_frame
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T02:27:42.109746+00:00
-- url     : https://prove2.me/submissions/cae32d1e-8913-4ac8-a574-15f688251d96

import Definitions.Def_mme_released_positive_integer_frame_data
import Theorems.Thm_mme_released_joint_interior_integer_constraints
import Theorems.Thm_mme_regional_reference_exists_iff_mass
import Theorems.Thm_mme_released_positive_region0_profile_reindex
import Theorems.Thm_mme_released_positive_region1_profile_reindex
import Theorems.Thm_mme_released_positive_region2_profile_reindex
import Theorems.Thm_mme_released_positive_region3_profile_reindex
import Theorems.Thm_mme_released_positive_region4_profile_reindex
import Theorems.Thm_mme_released_positive_region5_profile_reindex
import Theorems.Thm_mme_released_positive_region_position_transport
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FinCases

open scoped BigOperators Classical
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.MoreAsymmetryExactSeed
set_option autoImplicit false

namespace PositiveIntegerFrameProof

private def splitEquiv {half : ℕ} {p q : Fin 3 → ℕ} (hp : p = q) :
    RecursiveThinSplit.Split half p ≃ RecursiveThinSplit.Split half q :=
  Equiv.cast (congrArg (RecursiveThinSplit.Split half) hp)

private theorem splitEquiv_apply {half : ℕ} {p q : Fin 3 → ℕ} (hp : p = q)
    (c : RecursiveThinSplit.Split half p) :
    splitEquiv hp c = Eq.mp (congrArg (RecursiveThinSplit.Split half) hp) c := rfl

private theorem splitEquiv_val {half : ℕ} {p q : Fin 3 → ℕ} (hp : p = q)
    (c : RecursiveThinSplit.Split half p) :
    (splitEquiv hp c).val = c.val := by
  cases hp
  rfl

private theorem splitEquiv_complement {half : ℕ} {p q : Fin 3 → ℕ} (hp : p = q)
    (ht : p 0 + p 1 + p 2 = 2 * half)
    (ht' : q 0 + q 1 + q 2 = 2 * half)
    (c : RecursiveThinSplit.Split half p) :
    splitEquiv hp (complement ht c) = complement ht' (splitEquiv hp c) := by
  cases hp
  rfl

/-- Restriction to labels with positive sizes transports every finite
constraint before the large released tables are instantiated. -/
private theorem transport_constraints {half ell R S : ℕ}
    {parent : Fin R → Fin 3 → ℕ} {parent' : Fin S → Fin 3 → ℕ}
    (total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (total' : ∀ r, parent' r 0 + parent' r 1 + parent' r 2 = 2 * half)
    {n : Fin R → ℕ} {n' : Fin S → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (m' : ∀ r, RecursiveThinSplit.Split half (parent' r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (mu' : Fin 3 → Cell half S parent' → CompleteWord ell → ℕ)
    (select : Fin S → Fin R) (hp : ∀ r, parent' r = parent (select r))
    (hn : ∀ r, n' r = n (select r))
    (hm : ∀ r c, m' r c = m (select r) (splitEquiv (hp r) c))
    (hmu : ∀ i r c w, mu' i ⟨r,c⟩ w = mu i ⟨select r,splitEquiv (hp r) c⟩ w)
    (positive : ∀ r, 0 < n' r) (minimum : ℕ)
    (common_constraints :
      ∃ reference : RecursiveXHash.Address half R parent n,
        reference ∈ RecursiveXHash.target m ∧
        (∀ i c, ∑ w, mu i c w =
          m c.1 c.2 + m c.1 (complement (total c.1) c.2)) ∧
        (∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val) ∧
        BoundaryProfiles mu ∧
        (∀ r, n r ≠ 0 → minimum ≤ n r) ∧
        (∀ r c, minimum ∣ m r c)) :
    (∃ a : RecursiveXHash.Address half S parent' n', a ∈ RecursiveXHash.target m') ∧
    (∀ i c, ∑ w, mu' i c w =
      m' c.1 c.2 + m' c.1 (complement (total' c.1) c.2)) ∧
    (∀ i c w, 0 < mu' i c w → ∑ h, (w h).val = (c.2.val i).val) ∧
    BoundaryProfiles mu' ∧
    (∀ r, minimum ≤ n' r) ∧
    (∀ r c, minimum ∣ m' r c) := by
  classical
  obtain ⟨reference, reference_target, mass, support, boundary,
    parent_size, split_divisible⟩ := common_constraints
  have common_mass := (mme_regional_reference_exists_iff_mass m).mp ⟨reference, reference_target⟩
  have compact_mass : ∀ r, ∑ c, m' r c = n' r := by
    intro r
    calc
      (∑ c, m' r c) = ∑ c, m (select r) (splitEquiv (hp r) c) := by
        apply Finset.sum_congr rfl
        intro c _
        exact hm r c
      _ = ∑ c, m (select r) c := Equiv.sum_comp (splitEquiv (hp r)) (m (select r))
      _ = n (select r) := common_mass (select r)
      _ = n' r := (hn r).symm
  have cast_complement (r : Fin S) (c : RecursiveThinSplit.Split half (parent' r)) :
      splitEquiv (hp r) (complement (total' r) c) =
        complement (total (select r)) (splitEquiv (hp r) c) :=
    splitEquiv_complement (hp r) (total' r) (total (select r)) c
  refine ⟨(mme_regional_reference_exists_iff_mass m').mpr compact_mass, ?_, ?_, ?_, ?_, ?_⟩
  · intro i c
    rcases c with ⟨r,c⟩
    simpa only [← hmu, ← cast_complement, ← hm] using mass i ⟨select r,splitEquiv (hp r) c⟩
  · intro i c w hw
    rcases c with ⟨r,c⟩
    have hw' : 0 < mu i ⟨select r,splitEquiv (hp r) c⟩ w := by
      rwa [← hmu]
    simpa only [splitEquiv_val] using support i ⟨select r,splitEquiv (hp r) c⟩ w hw'
  · refine ⟨?_, ?_, ?_⟩
    · rintro ⟨r,c⟩ hz w
      have hz' : ((splitEquiv (hp r) c).val 2).val = 0 := by
        simpa only [splitEquiv_val] using hz
      simpa only [← hmu] using boundary.1 ⟨select r,splitEquiv (hp r) c⟩ hz' w
    · rintro ⟨r,c⟩ hz w
      have hz' : ((splitEquiv (hp r) c).val 0).val = 0 := by
        simpa only [splitEquiv_val] using hz
      simpa only [← hmu] using boundary.2.1 ⟨select r,splitEquiv (hp r) c⟩ hz' w
    · rintro ⟨r,c⟩ hz w
      have hz' : ((splitEquiv (hp r) c).val 1).val = 0 := by
        simpa only [splitEquiv_val] using hz
      simpa only [← hmu] using boundary.2.2 ⟨select r,splitEquiv (hp r) c⟩ hz' w
  · intro r
    have hnonzero : n (select r) ≠ 0 := by
      rw [← hn r]
      exact (positive r).ne'
    simpa only [← hn r] using parent_size (select r) hnonzero
  · intro r c
    simpa only [← hm r c] using split_divisible (select r) (splitEquiv (hp r) c)

private noncomputable def hashPositions {R B : ℕ} {n : Fin R → ℕ}
    (positions : Fin (B * 2) ≃ Position n) (label : Fin R) (positive : 0 < n label) :
    Fin (B - 1 + 1) ≃ (r : Fin R) × Fin (n r) := by
  classical
  have twice : B * 2 = (∑ r, n r) * 2 := by
    simpa only [Fintype.card_fin, Fintype.card_sigma, Fintype.card_prod,
      ← Finset.sum_mul] using Fintype.card_congr positions
  have mass : B = ∑ r, n r := by omega
  have single : n label ≤ ∑ r, n r :=
    Finset.single_le_sum (fun r _ => Nat.zero_le (n r)) (Finset.mem_univ label)
  have positive_blocks : 0 < B := by omega
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_fin, Fintype.card_sigma]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ B)]
  exact mass

private theorem profile_counts (region : Fin 6) :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size region 1 j})
      (hp : ∀ r, RecStage.parent3 region r = ReleasedJointInterior.parent region (e r).val),
      ∀ k : ℕ,
        (∀ r, ReleasedJointInterior.size region k (e r).val = k * RecStage.n3 region r) ∧
        (∀ (r : Fin 88) (c : RecursiveThinSplit.Split 4 (RecStage.parent3 region r)),
          ReleasedJointInterior.splitCount region k (e r).val
            (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hp r)) c) =
              k * RecStage.m3 region r c) ∧
        (∀ (i : Fin 3) (r : Fin 88)
          (c : RecursiveThinSplit.Split 4 (RecStage.parent3 region r)) (w : CompleteWord 2),
          ReleasedJointInterior.integerProfile region k i
            ⟨(e r).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hp r)) c⟩ w =
              k * RecStage.mu3 region i ⟨r,c⟩ w) := by
  fin_cases region
  · exact mme_released_positive_region0_profile_reindex
  · exact mme_released_positive_region1_profile_reindex
  · exact mme_released_positive_region2_profile_reindex
  · exact mme_released_positive_region3_profile_reindex
  · exact mme_released_positive_region4_profile_reindex
  · exact mme_released_positive_region5_profile_reindex

end PositiveIntegerFrameProof

-- The name linter otherwise unfolds concrete profile tables while inspecting binders.
set_option linter.constructorNameAsVariable false in
/-- The fixed compact data admit a positive integer frame before any
tolerance, repair scale, or output-rate budget is chosen. -/
theorem solution (region : Fin 6) (k : ℕ) (hk : 0 < k) :
    Nonempty (MME.ReleasedPositiveInteger.Frame region k) := by
  classical
  obtain ⟨e, hp, hcounts⟩ := PositiveIntegerFrameProof.profile_counts region
  obtain ⟨hn, hm, hmu⟩ := hcounts k
  have positive : ∀ r, 0 < k * RecStage.n3 region r := by
    intro r
    have hscale : ReleasedJointInterior.size region k (e r).val =
        k * ReleasedJointInterior.size region 1 (e r).val := by
      simp [ReleasedJointInterior.size, Nat.mul_assoc]
    rw [← hn r, hscale]
    exact Nat.mul_pos hk (e r).property
  have split_match : ∀ r c, k * RecStage.m3 region r c =
      ReleasedJointInterior.splitCount region k (e r).val
        (PositiveIntegerFrameProof.splitEquiv (hp r) c) := by
    intro r c
    simpa only [PositiveIntegerFrameProof.splitEquiv_apply] using (hm r c).symm
  have profile_match : ∀ i r c w, k * RecStage.mu3 region i ⟨r,c⟩ w =
      ReleasedJointInterior.integerProfile region k i
        ⟨(e r).val,PositiveIntegerFrameProof.splitEquiv (hp r) c⟩ w := by
    intro i r c w
    simpa only [PositiveIntegerFrameProof.splitEquiv_apply] using (hmu i r c w).symm
  obtain ⟨⟨reference, reference_target⟩, mass, support, boundary, parent_size, split_divisible⟩ :=
    PositiveIntegerFrameProof.transport_constraints
      (half := 4) (ell := 2) (R := 270) (S := 88)
      (parent := ReleasedJointInterior.parent region) (parent' := RecStage.parent3 region)
      (n := ReleasedJointInterior.size region k) (n' := fun r => k * RecStage.n3 region r)
      (ReleasedJointInterior.parent_total region) (RecStage.htotal3 region)
      (ReleasedJointInterior.splitCount region k) (fun r c => k * RecStage.m3 region r c)
      (ReleasedJointInterior.integerProfile region k) (fun i c w => k * RecStage.mu3 region i c w)
      (fun r => (e r).val) hp (fun r => (hn r).symm) split_match profile_match
      positive (k * denominator ^ 2)
      (mme_released_joint_interior_integer_constraints region k hk)
  obtain ⟨_, q, _, _, _, parent_graded, typical⟩ :=
    mme_released_positive_region_position_transport region k
  let positions := (ReleasedJointInterior.positions region k).trans q.symm
  exact ⟨{
    hashPositions := PositiveIntegerFrameProof.hashPositions positions 0 (positive 0)
    positions := positions
    reference := reference
    reference_target := reference_target
    mass := mass
    support := support
    boundary := boundary
    parent_size := parent_size
    split_divisible := split_divisible
    parent_graded := parent_graded
    typical := typical }⟩

#print axioms solution
