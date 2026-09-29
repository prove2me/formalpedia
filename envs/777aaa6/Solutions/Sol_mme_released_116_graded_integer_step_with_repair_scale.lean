-- Prove2me | solution 1 for mme_released_116_graded_integer_step_with_repair_scale
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T00:36:01.366109+00:00
-- url     : https://prove2.me/submissions/7e52656e-6caf-4266-a52d-24fc85ec786c

import Theorems.Thm_mme_released_116_scaled_reference_exists
import Theorems.Thm_mme_released_116_scaled_integer_divisibility
import Theorems.Thm_mme_released_116_integer_profile_mass
import Theorems.Thm_mme_released_116_integer_profile_support
import Theorems.Thm_mme_released_116_integer_profile_boundary
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases
import Theorems.Thm_mme_released_116_regional_total
import Theorems.Thm_mme_released_116_regional_split_mass
import Theorems.Thm_mme_released_116_weighted_parent_center
import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Fin.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false

/-- A partition of physical parent positions splits a full-word histogram
into the exact pair-word histograms of its regions. -/
private theorem mme_parent_histogram_sum_over_regions
    {P A W : Type} [Fintype P] {R : ℕ} {n : Fin R → ℕ}
    (positions : (Σ r, Fin (n r)) ≃ P) (f : P → A)
    (pair : A ≃ (Fin 2 → W)) (a : A) :
    Fintype.card {p : P // f p = a} =
      ∑ r, Fintype.card {t : Fin (n r) //
        ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h} := by
  classical
  have hinj : Function.Injective (fun p : (Σ r, {t : Fin (n r) //
      ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h}) =>
      (⟨p.1,p.2.val⟩ : Σ r, Fin (n r))) := by
    rintro ⟨r,t,ht⟩ ⟨s,u,hu⟩ heq
    cases heq
    rfl
  let e : (Σ r, {t : Fin (n r) //
      ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h}) ≃
      {p : P // f p = a} := {
    toFun := fun p => ⟨positions ⟨p.1,p.2.val⟩, pair.injective (funext p.2.property)⟩
    invFun := fun p => ⟨(positions.symm p.val).1,
      ⟨(positions.symm p.val).2, by
        intro h
        simp only [Sigma.eta, Equiv.apply_symm_apply, p.property]⟩⟩
    left_inv := by
      intro p
      apply hinj
      exact positions.symm_apply_apply ⟨p.1,p.2.val⟩
    right_inv := by intro p; apply Subtype.ext; exact positions.apply_symm_apply p.val }
  rw [← Fintype.card_congr e, Fintype.card_sigma]

/-- Regional parent windows imply the full-word histogram window around
the regional-size-weighted mean of their centers. -/
private theorem mme_regional_parent_windows_imply_global_histogram_window
    {P A W : Type} [Fintype P] [Fintype W]
    {half R T : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (positions : (Σ r, Fin (n r)) ≃ P) (f : P → A)
    (pair : A ≃ (Fin 2 → W)) (eps : ℝ)
    (hn : ∀ r, 0 < n r) (hT : ∑ r, n r = T) (hTpos : 0 < T)
    (htypical : parentTypical htotal n m mu eps
      (fun p => pair (f (positions ⟨p.1,p.2.1⟩)) p.2.2)) :
    ∀ a : A, |(Fintype.card {p : P // f p = a} : ℝ) / T -
      ∑ r, ((n r : ℝ) / T) * parentMixture htotal n m mu r (pair a)| ≤ eps := by
  classical
  intro a
  let H (r : Fin R) := Fintype.card {t : Fin (n r) //
    ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h}
  have hcount := mme_parent_histogram_sum_over_regions positions f pair a
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hnr (r : Fin R) : (0 : ℝ) < n r := by exact_mod_cast hn r
  have hlocal (r : Fin R) :
      |(H r : ℝ) / n r - parentMixture htotal n m mu r (pair a)| ≤ eps :=
    (htypical r (pair a)).le
  have hid : (Fintype.card {p : P // f p = a} : ℝ) / T -
      ∑ r, ((n r : ℝ) / T) * parentMixture htotal n m mu r (pair a) =
      ∑ r, ((n r : ℝ) / T) *
        ((H r : ℝ) / n r - parentMixture htotal n m mu r (pair a)) := by
    rw [hcount, Nat.cast_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [H]
    field_simp [(hnr r).ne']
  rw [hid]
  calc
    _ ≤ ∑ r, |((n r : ℝ) / T) *
        ((H r : ℝ) / n r - parentMixture htotal n m mu r (pair a))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, ((n r : ℝ) / T) * eps := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul, abs_of_pos (div_pos (hnr r) hTr)]
      exact mul_le_mul_of_nonneg_left (hlocal r) (div_pos (hnr r) hTr).le
    _ = eps := by
      rw [← Finset.sum_mul, ← Finset.sum_div, ← Nat.cast_sum, hT,
        div_self hTr.ne', one_mul]


/-- Replicating every occurrence preserves each normalized child profile. -/
private theorem mme_cell_frequency_scale
    {C W : Type*} [Fintype W] (mu : C → W → ℕ)
    (k : ℕ) (hk : 0 < k) (c : C) (w : W) :
    cellFrequency (fun c w => k * mu c w) c w = cellFrequency mu c w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [cellFrequency, ← Finset.mul_sum, Nat.cast_mul]
  exact mul_div_mul_left _ _ hk'

/-- Uniform replication preserves the regional parent-mixture centers. -/
private theorem mme_parent_mixture_scale
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (k : ℕ) (hk : 0 < k) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c v => k * mu c v) r w = parentMixture htotal n m mu r w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [parentMixture, mme_cell_frequency_scale mu k hk, Nat.cast_mul,
    mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hk'


open MME.Released116 MME.MoreAsymmetryExactSeed MME.CompleteSplit

/-- At every positive integer scale, the six regional windows imply a
full-word histogram window centered at the same released distribution. -/
private theorem mme_released_116_scaled_partition_parent_window (k : ℕ) (hk : 0 < k) :
    ∃ positions : (Σ r : Fin 6, Fin (k * regionalSize r)) ≃
        Fin (k * denominator ^ 4),
      ∀ (i : Fin 3) (f : Fin (k * denominator ^ 4) → CompleteWord 3) (eps : ℝ),
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (fun p =>
            let v := (completeWordSplitEquiv 2 (by decide)) (f (positions ⟨p.1,p.2.1⟩))
            ![v.1,v.2] p.2.2) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) // f p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  classical
  have hT : (∑ r : Fin 6, k * regionalSize r) = k * denominator ^ 4 := by
    rw [← Finset.mul_sum, mme_released_116_regional_total]
  have hcard : Fintype.card (Σ r : Fin 6, Fin (k * regionalSize r)) =
      Fintype.card (Fin (k * denominator ^ 4)) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hT
  let positions := Fintype.equivOfCardEq hcard
  refine ⟨positions, ?_⟩
  intro i f eps htypical w
  let pair := (completeWordSplitEquiv 2 (by decide)).trans
    (finTwoArrowEquiv (CompleteWord 2)).symm
  have h := mme_regional_parent_windows_imply_global_histogram_window
    parent_total (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w)
    positions f pair eps
    (fun r => Nat.mul_pos hk (mme_released_116_regional_split_mass r).1)
    hT (Nat.mul_pos hk (by norm_num [denominator])) htypical w
  have hpair (v : CompleteWord 3) : pair v =
      ![((completeWordSplitEquiv 2 (by decide)) v).1,
        ((completeWordSplitEquiv 2 (by decide)) v).2] := rfl
  have hweight (r : Fin 6) :
      ((k * regionalSize r : ℕ) : ℝ) / (k * denominator ^ 4 : ℕ) =
        (regionalSize r : ℝ) / (denominator : ℝ) ^ 4 := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [Nat.cast_mul, Nat.cast_pow]
    exact mul_div_mul_left _ _ hk'
  simp only [mme_parent_mixture_scale _ _ _ _ k hk, hweight, hpair] at h
  rw [mme_released_116_weighted_parent_center i w] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h


/-- A partition of parent words induces a child-position order that agrees
with literal left/right splitting of the same fine word. -/
private theorem mme_regional_parent_partition_fine_coordinates
    {R T : ℕ} {n : Fin R → ℕ}
    (positions : (Σ r, Fin (n r)) ≃ Fin T) :
    ∃ childPositions : Fin (T * 2) ≃ Position n,
      ∀ (x : ProfiledCW.FineWord (T * 4)) (p : Position n),
        ProfiledCW.split childPositions (show (T * 2) * 2 ^ (2 - 1) = T * 4 by omega) x p =
          (let v := completeWordSplitEquiv 2 (by decide)
            (ProfiledCW.split (Equiv.refl (Fin T)) rfl x (positions ⟨p.1,p.2.1⟩))
          ![v.1,v.2] p.2.2) := by
  let e : Fin (T * 2) ≃ Position n := finProdFinEquiv.symm.trans
    ((positions.symm.prodCongr (Equiv.refl (Fin 2))).trans
      (Equiv.sigmaProdDistrib (fun r => Fin (n r)) (Fin 2)))
  refine ⟨e, ?_⟩
  rintro x ⟨r,t,h⟩
  funext j
  fin_cases h <;> fin_cases j <;>
    simp [ProfiledCW.split, e, completeWordSplitEquiv, fineWordSplitEquiv,
      Equiv.sigmaProdDistrib, finProdFinEquiv, Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_assoc]


/-- The scaled released histogram inclusion holds directly for the fine-word
splitting map required by an integer extraction step. -/
private theorem mme_released_116_scaled_fine_word_window (k : ℕ) (hk : 0 < k) :
    ∃ childPositions : Fin ((k * denominator ^ 4) * 2) ≃
        Position (fun r : Fin 6 => k * regionalSize r),
      ∀ (i : Fin 3) (x : ProfiledCW.FineWord ((k * denominator ^ 4) * 4)) (eps : ℝ),
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (ProfiledCW.split childPositions
            (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
              (k * denominator ^ 4) * 4 by omega) x) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  classical
  obtain ⟨positions, hwindow⟩ := mme_released_116_scaled_partition_parent_window k hk
  obtain ⟨childPositions, hsplit⟩ := mme_regional_parent_partition_fine_coordinates positions
  refine ⟨childPositions, ?_⟩
  intro i x eps htypical w
  have hfun := funext (hsplit x)
  rw [hfun] at htypical
  exact hwindow i (ProfiledCW.split (Equiv.refl _) rfl x) eps htypical w

private theorem mme_child_grading_implies_parent_grading
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n) (f : Position n → CompleteWord ell)
    (hf : Graded htotal i a f) (r : Fin R) (t : Fin (n r)) :
    (∑ h : Fin 2, ∑ q, (f ⟨r,t,h⟩ q).val) = parent r i := by
  rw [Fin.sum_univ_two, hf, hf]
  simp only [fullCell, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  change ((a r t).val i).val + (parent r i - ((a r t).val i).val) = parent r i
  exact Nat.add_sub_of_le ((a r t).property.2 i)


private theorem grade_split_three (w : CompleteWord 3) :
    (∑ q, (w q).val) = ∑ h : Fin 2, ∑ q,
      ((![(completeWordSplitEquiv 2 (by decide) w).1,
        (completeWordSplitEquiv 2 (by decide) w).2] h) q).val := by
  simp [Fin.sum_univ_succ, completeWordSplitEquiv, fineWordSplitEquiv]
  omega

/-- The released histogram window and exact parent grades hold for the same
physical fine word whenever its child words satisfy the parent grades and are parent typical. -/
private theorem mme_released_116_scaled_parent_graded_fine_word_window (k : ℕ) (hk : 0 < k) :
    ∃ childPositions : Fin ((k * denominator ^ 4) * 2) ≃
        Position (fun r : Fin 6 => k * regionalSize r),
      ∀ (i : Fin 3)
        (x : ProfiledCW.FineWord ((k * denominator ^ 4) * 4)) (eps : ℝ),
        ParentGraded parent (fun r => k * regionalSize r) i (ProfiledCW.split childPositions
          (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
            (k * denominator ^ 4) * 4 by omega) x) →
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (ProfiledCW.split childPositions
            (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
              (k * denominator ^ 4) * 4 by omega) x) →
        (∀ p : Fin (k * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p q).val)
            = parent 0 i) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  classical
  obtain ⟨positions, hwindow⟩ := mme_released_116_scaled_partition_parent_window k hk
  obtain ⟨childPositions, hsplit⟩ := mme_regional_parent_partition_fine_coordinates positions
  refine ⟨childPositions, ?_⟩
  intro i x eps hg ht
  constructor
  · intro p
    obtain ⟨⟨r,t⟩, rfl⟩ := positions.surjective p
    have h := hg r t
    simp only [hsplit] at h
    rw [grade_split_three]
    exact h
  · have hfun := funext (hsplit x)
    rw [hfun] at ht
    exact hwindow i (ProfiledCW.split (Equiv.refl _) rfl x) eps ht



open MME.RegionRate MME.ProfiledCW MME.RecursiveYZ.CWCells

/-- Package the released profiles into the graded integer-step interface used by
recursive logarithmic recipes, retaining the exact copy formula and output. -/
theorem solution
    (d : ℕ) (hd : 1 < d) (k : ℕ) (hk : 0 < k) (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * 6 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2) ≤
      (k * denominator ^ 2 : ℕ) * eps ^ 2) :
    let n := fun r : Fin 6 => k * regionalSize r
    let m := fun r c => k * splitCount r c
    let mu := fun i c w => k * integerProfile i c w
    let source : Predicate ((k * denominator ^ 4) * 4) := fun i x =>
      (∀ p : Fin (k * denominator ^ 4),
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) = parent 0 i) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin (k * denominator ^ 4) //
            ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) /
            (k * denominator ^ 4 : ℕ) -
          ((((ReleasedGlobal.jointRows 0 10).map
            (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ) ^ 4| ≤ eps
    ∃ (positions : Fin ((k * denominator ^ 4) * 2) ≃ Position n)
      (reference : Address 4 6 parent n), reference ∈ RecursiveXHash.target m ∧
      ∃ D : IntegerStepG 2 ((k * denominator ^ 4) * 4) source,
        D.step.certifiedLogCopies =
          regionalRate parent_total n m mu - ((∑ r, n r : ℕ) : ℝ) *
            entropyModulus (Fin 2 → CompleteWord 2) eps -
          4 * Real.sqrt (Real.log (scaleFactor (half := 4) (parent := parent) n d 2) +
            scaleExponent parent_total n m mu eps) -
          Real.log (64 * polynomialFactor n (Fintype.card (Cell 4 6 parent)) *
            scaleFactor (half := 4) (parent := parent) n d 2) -
          ((Nat.log d (∏ i : Fin 3, Nat.card (Block 2 (fullCell parent_total reference)
            (fun c i => (c.2.val i).val) mu i)) + 1 : ℕ) : ℝ) * Real.log 8 ∧
        D.step.output = fun i x => Graded parent_total i reference
          (ProfiledCW.split (ell := 2) positions (by omega) x) ∧
          Useful (fullCell parent_total reference) (mu i)
            (ProfiledCW.split (ell := 2) positions (by omega) x) := by
  classical
  dsimp only
  obtain ⟨positions, hwindow⟩ := mme_released_116_scaled_parent_graded_fine_word_window k hk
  obtain ⟨reference, href⟩ := mme_released_116_scaled_reference_exists k
  have hT : 0 < k * denominator ^ 4 := Nat.mul_pos hk (by norm_num [denominator])
  have hcard : Fintype.card (Σ r : Fin 6, Fin (k * regionalSize r)) =
      k * denominator ^ 4 := by
    simp only [Fintype.card_sigma, Fintype.card_fin, ← Finset.mul_sum,
      mme_released_116_regional_total]
  let e : Fin ((k * denominator ^ 4 - 1) + 1) ≃
      (Σ r : Fin 6, Fin (k * regionalSize r)) :=
    (finCongr (Nat.sub_add_cancel hT)).trans (Fintype.equivFinOfCardEq hcard).symm
  have hmass : ∀ i c, ∑ w, k * integerProfile i c w =
      k * splitCount c.1 c.2 + k * splitCount c.1 (complement (parent_total c.1) c.2) := by
    intro i c
    rw [← Finset.mul_sum, mme_released_116_integer_profile_mass, Nat.mul_add]
  have hsupport : ∀ i c w, 0 < k * integerProfile i c w →
      ∑ h, (w h).val = (c.2.val i).val := by
    intro i c w hw
    exact mme_released_116_integer_profile_support i c w (Nat.pos_of_mul_pos_left hw)
  have hboundary : BoundaryProfiles (fun i c w => k * integerProfile i c w) := by
    refine ⟨?_, ?_, ?_⟩
    · intro c hc w
      exact congrArg (k * ·) (mme_released_116_integer_profile_boundary.1 c hc w)
    · intro c hc w
      exact congrArg (k * ·) (mme_released_116_integer_profile_boundary.2.1 c hc w)
    · intro c hc w
      exact congrArg (k * ·) (mme_released_116_integer_profile_boundary.2.2 c hc w)
  obtain ⟨hminimum, hsize, hdiv⟩ := mme_released_116_scaled_integer_divisibility k hk
  let band : Predicate ((k * denominator ^ 4) * 4) := fun i x =>
    parentTypical parent_total (fun r => k * regionalSize r)
      (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
      (ProfiledCW.split (ell := 2) positions (by omega) x)
  let S : IntegerStep 2 ((k * denominator ^ 4) * 4) band := {
    half := 4
    R := 6
    parent := parent
    n := fun r => k * regionalSize r
    total := parent_total
    half_eq := by decide
    m := fun r c => k * splitCount r c
    N := k * denominator ^ 4 - 1
    hashPositions := e
    L := (k * denominator ^ 4) * 2
    positions := positions
    length := by omega
    mu := fun i c w => k * integerProfile i c w
    mass := hmass
    support := hsupport
    boundary := hboundary
    reference := reference
    reference_target := href
    minimum := k * denominator ^ 2
    repairScale := d
    minimum_pos := hminimum
    repairScale_gt_one := hd
    parent_size := hsize
    split_divisible := hdiv
    epsilon := eps
    epsilon_pos := heps
    size_test := hscale
    source_inside := fun _ _ h => h }
  refine ⟨positions, reference, href, ⟨band, S, ?_⟩, rfl, rfl⟩
  intro i x hg ht
  exact hwindow i x eps hg ht


#print axioms solution
