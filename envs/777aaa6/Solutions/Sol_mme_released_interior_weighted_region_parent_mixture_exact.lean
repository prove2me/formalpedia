-- Prove2me | solution 1 for mme_released_interior_weighted_region_parent_mixture_exact
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:15:42.311169+00:00
-- url     : https://prove2.me/submissions/f60feddd-fa11-4a01-b62d-9a6ef3a87353

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_released_global_profile_data
import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
import Mathlib.Data.List.Sort

set_option autoImplicit false
namespace MME.ReleasedInterior
open MoreAsymmetryExactSeed



/-- Every square-child distribution used by an interior released recipe has
exact mass equal to the common denominator, including children in zero-weight
regions. Complementary splits occur in the same split list. -/
private theorem mme_released_interior_child_mass (owner : Fin 6) (s : Fin 45) :
    (seed owner s).boundary = [] →
      ∀ (j : Fin 6) (shape : List ℕ), shape ∈ (seed owner s).splits →
        ((child (seed owner s) j.val shape).map Prod.snd).sum = denominator := by
  fin_cases owner
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

open BigOperators MME.RecursiveYZ MME.CompleteSplit

private theorem inverse_role_apply : ∀ (owner : Fin 6) (i : Fin 3),
    inverseRole owner (role owner i) = i := by decide +kernel



private theorem source_shape_mem (owner : Fin 6) (s : Fin 45) :
    (seed owner s).boundary = [] →
      ∀ c : Split s, sourceShape owner c ∈ (seed owner s).splits := by
  fin_cases owner
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

private theorem marginal_mass (owner : Fin 6) (L : List (ℕ × ℕ)) (i : Fin 3) :
    (∑ w : CompleteWord 2,
      (L.map (fun a => if childWord owner a.1 i = w then a.2 else 0)).sum) =
      (L.map Prod.snd).sum := by
  classical
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]
    simp

/-- The actual integer child profiles have the exact mass of the two
complementary child occurrences, for every released interior component. -/
private theorem mme_released_interior_integer_profile_mass
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (i : Fin 3) (c : Cell 4 6 (parent s)) :
    ∑ w, integerProfile owner s i c w =
      splitCount owner s c.1 c.2 +
        splitCount owner s c.1 (complement (parent_total s c.1) c.2) := by
  simp only [integerProfile, childMarginal, ← Finset.mul_sum, marginal_mass]
  rw [mme_released_interior_child_mass owner s hi c.1 _
    (source_shape_mem owner s hi c.2)]
  simp only [splitCount]
  ring

private theorem child_mem_grade (t : Term) (j : ℕ) (shape : List ℕ)
    (p : ℕ × ℕ) (hp : p ∈ child t j shape) :
    List.ofFn (fun i : Fin 3 =>
      (ReleasedGlobal.elementary ⟨p.1 % 6, Nat.mod_lt _ (by decide)⟩ i).val +
      (ReleasedGlobal.elementary ⟨p.1 / 6 % 6, Nat.mod_lt _ (by decide)⟩ i).val) = shape := by
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hp
  have hfst : a = p.1 := congrArg Prod.fst heq
  have hgrade := (List.mem_filter.mp ha).2
  simpa only [hfst, beq_iff_eq] using hgrade

private theorem child_word_grade (owner : Fin 6) (s : Fin 45) (r : Fin 6)
    (c : Split s) (p : ℕ × ℕ)
    (hp : p ∈ child (seed owner s) r.val (sourceShape owner c)) (i : Fin 3) :
    ∑ h, (childWord owner p.1 i h).val = (c.val i).val := by
  have h := child_mem_grade _ _ _ p hp
  unfold sourceShape at h
  have hvec := List.ofFn_injective h
  have hi := congrFun hvec (role owner i)
  change (∑ h : Fin 2, (childWord owner p.1 i h).val) = (c.val i).val
  rw [Fin.sum_univ_two]
  simpa only [inverse_role_apply, childWord,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, Nat.div_one] using hi

/-- Positive child counts have the actual child grade after applying the
owner's coordinate permutation. This includes all supported interior shapes. -/
private theorem mme_released_interior_integer_profile_support
    (owner : Fin 6) (s : Fin 45) (i : Fin 3)
    (c : Cell 4 6 (parent s)) (w : CompleteWord 2)
    (hw : 0 < integerProfile owner s i c w) :
    ∑ h, (w h).val = (c.2.val i).val := by
  by_contra hn
  have hz : childMarginal owner s c.1 c.2 i w = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have hne : childWord owner a.1 i ≠ w := by
      intro heq
      exact hn (heq ▸ child_word_grade owner s c.1 c.2 a ha i)
    simp only [if_neg hne]
  simp only [integerProfile, hz, mul_zero] at hw
  exact (Nat.lt_irrefl 0) hw


/-- Every typed child split has positive alpha weight, even in an empty region. -/
private theorem split_weight_pos (owner : Fin 6) (s : Fin 45) :
    (seed owner s).boundary = [] →
      ∀ (r : Fin 6) (c : Split s), 0 < splitWeight owner s r c := by
  fin_cases owner
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

/-- In a nonempty region, normalization cancels the regional and complementary
split scales and recovers the released child marginal. -/
private theorem mme_released_interior_integer_profile_frequency
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (i : Fin 3) (c : Cell 4 6 (parent s))
    (hr : regionalSize owner s c.1 ≠ 0) (w : CompleteWord 2) :
    RegionRealization.cellFrequency (integerProfile owner s i) c w =
      (childMarginal owner s c.1 c.2 i w : ℝ) / denominator := by
  have hregion : 0 < (seed owner s).region.getD c.1.val 0 := by
    by_contra h
    have hz : (seed owner s).region.getD c.1.val 0 = 0 := by omega
    exact hr (by simp only [regionalSize, hz, zero_mul])
  let K := (seed owner s).region.getD c.1.val 0 *
    (splitWeight owner s c.1 c.2 +
      splitWeight owner s c.1 (complement (parent_total s c.1) c.2)) * denominator
  have hpos : 0 < K := by
    exact Nat.mul_pos (Nat.mul_pos hregion
      (Nat.add_pos_left (split_weight_pos owner s hi c.1 c.2) _))
      (by norm_num [denominator])
  have hmass : ∑ v, integerProfile owner s i c v = K * denominator := by
    rw [mme_released_interior_integer_profile_mass owner s hi]
    dsimp [splitCount, K]
    ring
  unfold RegionRealization.cellFrequency
  rw [hmass]
  change ((K * childMarginal owner s c.1 c.2 i w : ℕ) : ℝ) /
    ((K * denominator : ℕ) : ℝ) = _
  simp only [Nat.cast_mul]
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos))

/-- Empty regions have zero child frequencies under the totalized division
convention, so no positivity hypothesis is silently imposed on a recipe. -/
private theorem mme_released_interior_empty_region_frequency
    (owner : Fin 6) (s : Fin 45) (i : Fin 3) (c : Cell 4 6 (parent s))
    (hr : regionalSize owner s c.1 = 0) (w : CompleteWord 2) :
    RegionRealization.cellFrequency (integerProfile owner s i) c w = 0 := by
  have hz : (seed owner s).region.getD c.1.val 0 = 0 := by
    simpa [regionalSize, denominator] using hr
  simp only [RegionRealization.cellFrequency, integerProfile, hz, zero_mul, Nat.cast_zero,
    zero_div]


end MME.ReleasedInterior
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

/-- Weighting by the region size gives the released product of child marginals.
The identity also holds for empty regions, whose contribution is zero. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (i : Fin 3) (r : Fin 6) (w : Fin 2 → CompleteWord 2) :
    ((regionalSize owner s r : ℝ) / (denominator : ℝ) ^ 4) *
      RegionRealization.parentMixture (parent_total s)
        (regionalSize owner s) (splitCount owner s) (integerProfile owner s i) r w =
    ((seed owner s).region.getD r.val 0 : ℝ) / (denominator : ℝ) ^ 4 *
      ∑ c : Split s, (splitWeight owner s r c : ℝ) *
        (childMarginal owner s r c i (w 0) : ℝ) *
        (childMarginal owner s r (complement (parent_total s r) c) i (w 1) : ℝ) := by
  by_cases hr : regionalSize owner s r = 0
  · have hz : (seed owner s).region.getD r.val 0 = 0 := by
      simpa [regionalSize, denominator] using hr
    simp only [hr, hz, Nat.cast_zero, zero_div, zero_mul]
  · have hn : (regionalSize owner s r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
    have hd : (denominator : ℝ) ≠ 0 := by norm_num [denominator]
    have hf (c : Split s) (v : CompleteWord 2) :
        RegionRealization.cellFrequency (integerProfile owner s i) ⟨r, c⟩ v =
          (childMarginal owner s r c i v : ℝ) / denominator :=
      mme_released_interior_integer_profile_frequency owner s hi i ⟨r, c⟩ hr v
    unfold RegionRealization.parentMixture
    simp_rw [hf]
    rw [mul_comm ((regionalSize owner s r : ℝ) / (denominator : ℝ) ^ 4),
      div_mul_div_cancel₀ hn]
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    dsimp [splitCount]
    push_cast
    field_simp
    simp only [parent, RecursiveYZ.complement]


#print axioms solution
