-- Prove2me | solution 1 for mme_released_interior_graded_histogram_exact_step_with_repair_scale
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:20:57.829571+00:00
-- url     : https://prove2.me/submissions/1f594c68-3ad7-4b4c-aadc-3903b5741140

import Theorems.Thm_mme_released_interior_scaled_graded_fine_word_window
import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact
import Theorems.Thm_mme_recursive_region_graded_source_exact_step_allow_empty
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization MME.ProfiledCW MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical

private theorem split_flatten {S : Type} {ell L M : ℕ} (positions : Fin L ≃ S)
    (length : L * 2 ^ (ell - 1) = M) (f : S → CompleteSplit.CompleteWord ell) :
    ProfiledCW.split positions length (ProfiledCW.flatten positions length f) = f := by
  funext p h
  simp [ProfiledCW.split, ProfiledCW.flatten]

theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (d : ℕ) (hd : 1 < d) (k : ℕ) (hk : 0 < k) (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * 6 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2) ≤
      (k * denominator ^ 2 : ℕ) * eps ^ 2) :
    let n := fun r : Fin 6 => k * (regionalSize owner s) r
    let m := fun r c => k * (splitCount owner s) r c
    let mu := fun i c w => k * (integerProfile owner s) i c w
    let source : Predicate ((k * denominator ^ 4) * 4) := fun i x =>
      (∀ p : Fin (k * denominator ^ 4),
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) = (parent s) 0 i) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin (k * denominator ^ 4) //
            ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) /
            (k * denominator ^ 4 : ℕ) -
          ((((ReleasedGlobal.jointRows owner s).map
            (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ) ^ 4| ≤ eps
    let keep := fun (i : Fin 2) (_ : Address 4 6 (parent s) n) =>
      parentTypical (parent_total s) n m (mu (yzMode i)) eps
    let Q := commonScale 4 (loadNum (parent_total s) m d (fun i => mu (yzMode i)) keep) (loadDen m)
    ∃ (positions : Fin ((k * denominator ^ 4) * 2) ≃ Position n)
      (reference : Address 4 6 (parent s) n), reference ∈ RecursiveXHash.target m ∧
      ∃ E : ExactStep 2 ((k * denominator ^ 4) * 4) source,
        ((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell (parent_total s) reference)
            (fun c i => (c.2.val i).val) mu i)) + 1 ∧
        E.output = fun i x => Graded (parent_total s) i reference
          (ProfiledCW.split (ell := 2) positions (by omega) x) ∧
          Useful (fullCell (parent_total s) reference) (mu i)
            (ProfiledCW.split (ell := 2) positions (by omega) x)  := by
  classical
  dsimp only
  obtain ⟨positions, hwindow⟩ :=
    mme_released_interior_scaled_graded_fine_word_window owner s hi k hk
  obtain ⟨reference, href, htotal, hmass, hsupport, hboundary, hminimum, hsize, hdiv⟩ :=
    mme_released_interior_scaled_integer_profile_constraints_exact owner s hi k hk
  have hT : 0 < k * denominator ^ 4 := Nat.mul_pos hk (by norm_num [denominator])
  have hcard : Fintype.card (Σ r : Fin 6, Fin (k * regionalSize owner s r)) =
      k * denominator ^ 4 := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using htotal
  let e : Fin ((k * denominator ^ 4 - 1) + 1) ≃
      (Σ r : Fin 6, Fin (k * regionalSize owner s r)) :=
    (finCongr (Nat.sub_add_cancel hT)).trans (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨positions, reference, href, ?_⟩
  apply mme_recursive_region_graded_source_exact_step_allow_empty (parent s)
    (fun r => k * regionalSize owner s r) (parent_total s) (by decide)
    (fun r c => k * splitCount owner s r c) e positions (by omega)
    (fun i c w => k * integerProfile owner s i c w) hmass hsupport hboundary reference href
    (k * denominator ^ 2) d hminimum hd hsize hdiv eps heps hscale _
  intro i a ha f hg ht
  have h := hwindow i a (ProfiledCW.flatten positions (by omega) f) eps
  rw [split_flatten] at h
  exact h hg ht


#print axioms solution
