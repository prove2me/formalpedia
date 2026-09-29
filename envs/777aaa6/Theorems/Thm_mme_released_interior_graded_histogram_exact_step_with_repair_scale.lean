-- Prove2me | Theorems.Thm_mme_released_interior_graded_histogram_exact_step_with_repair_scale
-- name    : mme_released_interior_graded_histogram_exact_step_with_repair_scale
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:18:24.51845+00:00
-- url     : https://prove2.me/theorems/31698a84-6cf3-416c-b30c-f215685a5df4
-- title:
--   Quantitative exact extraction for every released interior recipe
-- statement:
--   At every positive replication satisfying the stated concentration inequality, each released interior recipe supplies an exact extraction step from its graded global histogram window. The statement retains the selected-count lower bound, logarithmic repair exponent, and exact graded useful output, including empty regions. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_scaled_graded_fine_word_window
import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact
import Theorems.Thm_mme_recursive_region_graded_source_exact_step_allow_empty
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization MME.ProfiledCW MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical

theorem mme_released_interior_graded_histogram_exact_step_with_repair_scale
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
            (ProfiledCW.split (ell := 2) positions (by omega) x)  := by sorry
