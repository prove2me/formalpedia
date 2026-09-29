-- Prove2me | solution 1 for mme_released_global_parent_cofinal_matrix_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T03:14:55.824009+00:00
-- url     : https://prove2.me/submissions/99e70176-2a43-437b-81fb-b6577902e72c

import Definitions.Def_mme_six_symmetrized_tau_value
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
private theorem mme_released_global_conditional_histogram_center
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


open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
universe u

private theorem released_global_conditional_center
    (owner : Fin 6) (s : Fin 45) (ha0 : 0 < alpha owner s)
    (t : ℕ) (ht : 0 < t) (i : Fin 3) (w : Word) :
    ((blocks t : ℝ) / ((t * coarseCounts owner (shapeEquiv s) : ℕ) : ℝ)) *
        (profile owner).2 i ⟨0,shapeEquiv s⟩ w =
      ((((jointRows owner s).map
        (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℝ) /
          (denominator : ℝ)^4 := by
  have ha : 0 < alpha owner (shapeEquiv.symm (shapeEquiv s)) := by
    simpa only [Equiv.symm_apply_apply] using ha0
  simpa only [Equiv.symm_apply_apply] using
    mme_released_global_conditional_histogram_center owner (shapeEquiv s) ha t ht i w

private theorem released_global_tolerance_match (owner : Fin 6) (s : Fin 45)
    (ha0 : 0 < alpha owner s) (t : ℕ) (ht : 0 < t) (eps : ℝ) :
    ((blocks t : ℝ) / ((t * coarseCounts owner (shapeEquiv s) : ℕ) : ℝ)) *
      ((alpha owner s : ℝ) / denominator * eps) = eps := by
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht)
  have ha : (alpha owner s : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha0)
  have hd : (denominator : ℝ) ≠ 0 := by norm_num [denominator]
  simp only [blocks, coarseCounts, Equiv.symm_apply_apply, Nat.cast_mul, Nat.cast_pow]
  field_simp

/-- At the rescaled global tolerance, the actual normalized released cell tensor is
exactly the flat graded histogram source used by parent extraction. -/
private theorem mme_released_global_normalized_cell_eq_parent_source
    {K : Type u} [Field K] (owner : Fin 6) (s : Fin 45)
    (ha0 : 0 < alpha owner s) (t : ℕ) (ht : 0 < t) (eps : ℝ) :
    let L := t * coarseCounts owner (shapeEquiv s)
    (source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L)
      (fun i x =>
        (∀ r, grade (label 5 3 L (Equiv.refl _) x r) = ((shapeEquiv s).val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          (alpha owner s : ℝ) / denominator * eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / L -
          ((blocks t : ℝ) / L) * (profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          ((blocks t : ℝ) / L) * ((alpha owner s : ℝ) / denominator * eps)) =
    ProfiledCW.tensor K (fun i (x : ProfiledCW.FineWord (L * 4)) =>
      (∀ p : Fin L,
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
          ((shapeEquiv s).val i).val) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin L //
          ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / L -
          ((((jointRows owner s).map
            (fun a => if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ)^4| ≤ eps) := by
  classical
  dsimp only
  let L := t * coarseCounts owner (shapeEquiv s)
  have hL : L ≠ 0 := by
    have hc : 0 < coarseCounts owner (shapeEquiv s) := by
      simp only [coarseCounts, Equiv.symm_apply_apply]
      exact Nat.mul_pos ha0 (by norm_num [denominator])
    exact Nat.ne_of_gt (Nat.mul_pos ht hc)
  have hsplit (x : WordIndex.{u} 5 3 L) :
      label 5 3 L (Equiv.refl _) x =
        ProfiledCW.split (ell := 3) (Equiv.refl _) rfl (ProfiledCW.fine x) := by
    funext p q
    simp [label, ProfiledCW.split, ProfiledCW.fine]
  have hcount (f : Fin L → CompleteWord 3) (w : CompleteWord 3) :
      count (fun _ : Fin L => Unit.unit) f Unit.unit w =
        Fintype.card {p : Fin L // f p = w} := by
    simp [count, Fintype.card_subtype]
  change (source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) _ =
    (source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) _
  apply congrArg ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L))
  funext i x
  apply propext
  dsimp only [L] at hL hsplit hcount
  simp only [if_neg hL, hsplit, hcount,
    released_global_conditional_center owner s ha0 t ht,
    released_global_tolerance_match owner s ha0 t ht, CWCells.grade]


/-- A parent replication divisible by the released coarse weight yields a
positive global replication with exactly the same number of coarse blocks. -/
private theorem mme_released_global_scale_of_multiple
    (owner : Fin 6) (s : Fin 45) (hpos : 0 < alpha owner s)
    (K k : ℕ) (hk : 0 < k) (hdiv : alpha owner s ∣ k)
    (hK : alpha owner s * K ≤ k) :
    ∃ t : ℕ, K ≤ t ∧ 0 < t ∧ k = alpha owner s * t ∧
      t * coarseCounts owner (shapeEquiv s) = k * denominator^4 := by
  obtain ⟨t, ht⟩ := hdiv
  have htpos : 0 < t := by
    by_contra hn
    have : t = 0 := by omega
    simp [this] at ht
    omega
  have hKt : K ≤ t := by
    rw [ht] at hK
    by_contra hn
    have hl : t + 1 ≤ K := by omega
    have hh := Nat.mul_le_mul_left (alpha owner s) hl
    rw [Nat.mul_add, Nat.mul_one] at hh
    omega
  refine ⟨t, hKt, htpos, ht, ?_⟩
  simp only [coarseCounts, Equiv.symm_apply_apply, ht]
  ring



open MME.TensorObj
/-- Cofinal parent extractions at multiples of the coarse weight transfer to
cofinal extractions from the actual normalized global cell, preserving rate. -/
theorem solution
    {K : Type u} [Field K] (owner : Fin 6) (s : Fin 45)
    (ha : 0 < alpha owner s) (eps tau : ℝ) (rate : ℕ → ℝ) :
    let parent := fun m : ℕ =>
      let L := m * denominator^4
    ProfiledCW.tensor K (fun i (x : ProfiledCW.FineWord (L * 4)) =>
      (∀ p : Fin L,
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
          ((shapeEquiv s).val i).val) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin L //
          ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / L -
          ((((jointRows owner s).map
            (fun a => if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ)^4| ≤ eps)
    let cell := fun t : ℕ =>
      let L := t * coarseCounts owner (shapeEquiv s)
    (source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L)
      (fun i x =>
        (∀ r, grade (label 5 3 L (Equiv.refl _) x r) = ((shapeEquiv s).val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          (alpha owner s : ℝ) / denominator * eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / L -
          ((blocks t : ℝ) / L) * (profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          ((blocks t : ℝ) / L) * ((alpha owner s : ℝ) / denominator * eps))
    (∀ cutoff : ℕ, ∃ m : ℕ, cutoff ≤ m ∧ 0 < m ∧ alpha owner s ∣ m ∧
      ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
        Restrict (bigAdd (fun v => MMObj K (a v) (b v) (c v)))
          (sixSymmetrization (parent m)) ∧
        Real.exp (rate m) ≤ ∑ v, ((a v * b v * c v : ℕ) : ℝ)^tau) →
    ∀ cutoff : ℕ, ∃ t : ℕ, cutoff ≤ t ∧ 0 < t ∧
      ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
        Restrict (bigAdd (fun v => MMObj K (a v) (b v) (c v)))
          (sixSymmetrization (cell t)) ∧
        Real.exp (rate (alpha owner s * t)) ≤ ∑ v, ((a v * b v * c v : ℕ) : ℝ)^tau := by
  dsimp only
  intro hparent cutoff
  obtain ⟨m, hmcut, hmpos, hmdiv, copies, a, b, c, hcopies, hextract, hweight⟩ :=
    hparent (alpha owner s * cutoff)
  obtain ⟨t, htcut, htpos, hmt, hlength⟩ :=
    mme_released_global_scale_of_multiple owner s ha cutoff m hmpos hmdiv hmcut
  refine ⟨t, htcut, htpos, copies, a, b, c, hcopies, ?_, ?_⟩
  · have hbridge := mme_released_global_normalized_cell_eq_parent_source
      (K := K) owner s ha t htpos eps
    dsimp only at hbridge
    conv_rhs => rw [hbridge, hlength]
    exact hextract
  · simpa only [hmt] using hweight


#print axioms solution
