-- Prove2me | solution 1 for mme_released_interior_scaled_graded_fine_word_window
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:15:16.989757+00:00
-- url     : https://prove2.me/submissions/65026bdb-3b76-49c8-9e04-fb69fbab0a3f

import Theorems.Thm_mme_released_interior_scaled_partition_parent_window
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_complete_split_concatenation
import Definitions.Def_mme_released_interior_integer_profiles
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization
open scoped Classical
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
physical fine word whenever its child words are graded and parent typical. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (k : ℕ) (hk : 0 < k) :
    ∃ childPositions : Fin ((k * denominator ^ 4) * 2) ≃
        Position (fun r : Fin 6 => k * (regionalSize owner s) r),
      ∀ (i : Fin 3) (a : Address 4 6 (parent s) (fun r => k * (regionalSize owner s) r))
        (x : ProfiledCW.FineWord ((k * denominator ^ 4) * 4)) (eps : ℝ),
        Graded (parent_total s) i a (ProfiledCW.split childPositions
          (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
            (k * denominator ^ 4) * 4 by omega) x) →
        parentTypical (parent_total s) (fun r => k * (regionalSize owner s) r)
          (fun r c => k * (splitCount owner s) r c) (fun c w => k * (integerProfile owner s) i c w) eps
          (ProfiledCW.split childPositions
            (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
              (k * denominator ^ 4) * 4 by omega) x) →
        (∀ p : Fin (k * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p q).val)
            = (parent s) 0 i) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows owner s).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  classical
  obtain ⟨positions, hwindow⟩ := mme_released_interior_scaled_partition_parent_window owner s hi k hk
  obtain ⟨childPositions, hsplit⟩ := mme_regional_parent_partition_fine_coordinates positions
  refine ⟨childPositions, ?_⟩
  intro i a x eps hg ht
  constructor
  · intro p
    obtain ⟨⟨r,t⟩, rfl⟩ := positions.surjective p
    have h := mme_child_grading_implies_parent_grading (parent_total s) i a _ hg r t
    simp only [hsplit] at h
    rw [grade_split_three]
    exact h
  · have hfun := funext (hsplit x)
    rw [hfun] at ht
    exact hwindow i (ProfiledCW.split (Equiv.refl _) rfl x) eps ht


#print axioms solution
