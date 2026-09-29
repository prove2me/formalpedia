-- Prove2me | solution 1 for mme_released_global_conditional_histogram_center
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T02:31:48.057577+00:00
-- url     : https://prove2.me/submissions/b02efcca-9eb2-4dbe-aa67-17dce0d34e1a

import Definitions.Def_mme_released_global_frame_data

open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
set_option autoImplicit false

private theorem row_marginal_sum (L : List (Fin 1296 × ℕ)) (i : Fin 3) (w : Word) :
    (∑ v : JointWord, if v i = w then
      (L.map (fun a ↦ if atom a.1 = v then a.2 else 0)).sum else 0) =
      (L.map (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum := by
  classical
  induction L with
  | nil => simp
  | cons a L ih =>
    have hsum (v : JointWord) :
        (if v i = w then (if atom a.1 = v then a.2 else 0) +
          (L.map (fun a ↦ if atom a.1 = v then a.2 else 0)).sum else 0) =
        (if v i = w then (if atom a.1 = v then a.2 else 0) else 0) +
          (if v i = w then (L.map (fun a ↦ if atom a.1 = v then a.2 else 0)).sum
            else 0) := by
      by_cases h : v i = w <;> simp only [h, ite_true, ite_false, zero_add]
    simp only [List.map_cons, List.sum_cons]
    simp_rw [hsum]
    rw [Finset.sum_add_distrib, ih]
    have heq (v : JointWord) :
        (if v i = w then if atom a.1 = v then a.2 else 0 else 0) =
          if v = atom a.1 then (if atom a.1 i = w then a.2 else 0) else 0 := by
      by_cases hv : v = atom a.1
      · subst v; simp
      · simp [hv, Ne.symm hv]
    simp_rw [heq]
    simp

/-- The marginal of the released joint counts is the marginal of its finite
row list, multiplied by the coarse weight. This includes zero coarse weights. -/
private theorem mme_released_global_word_counts_row_marginal
    (owner : Fin 6) (c : Shape) (i : Fin 3) (w : Word) :
    wordCounts owner i c w = alpha owner (shapeEquiv.symm c) *
      ((jointRows owner (shapeEquiv.symm c)).map
        (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum := by
  classical
  unfold wordCounts jointCounts rowCounts
  rw [← row_marginal_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

/-- Conditioning the global histogram center on a positive coarse cell removes
the global replication and its coarse weight, leaving the released row marginal. -/
theorem solution
    (owner : Fin 6) (c : Shape) (hc : 0 < alpha owner (shapeEquiv.symm c))
    (k : ℕ) (hk : 0 < k) (i : Fin 3) (w : Word) :
    ((blocks k : ℝ) / ((k * coarseCounts owner c : ℕ) : ℝ)) *
        (profile owner).2 i ⟨0,c⟩ w =
      ((((jointRows owner (shapeEquiv.symm c)).map
        (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℝ) /
          (denominator : ℝ)^4 := by
  change ((blocks k : ℝ) / ((k * coarseCounts owner c : ℕ) : ℝ)) *
    ((wordCounts owner i c w : ℝ) / (denominator : ℝ)^5) = _
  rw [mme_released_global_word_counts_row_marginal]
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hcR : (alpha owner (shapeEquiv.symm c) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
  have hd : (denominator : ℝ) ≠ 0 := by norm_num [denominator]
  simp only [blocks, coarseCounts, Nat.cast_mul, Nat.cast_pow]
  field_simp


#print axioms solution
