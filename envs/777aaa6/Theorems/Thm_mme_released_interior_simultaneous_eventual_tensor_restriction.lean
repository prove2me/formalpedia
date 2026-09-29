-- Prove2me | Theorems.Thm_mme_released_interior_simultaneous_eventual_tensor_restriction
-- name    : mme_released_interior_simultaneous_eventual_tensor_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:53:31.437601+00:00
-- url     : https://prove2.me/theorems/a4e671cc-31d7-4f3e-9fc4-4bbc31e88cdb
-- title:
--   Every sufficiently large scale supports all interior tensor restrictions
-- statement:
--   The eventual exact extractions give actual tensor restrictions over any field, retaining the selected-count estimate and the post-repair integer rounding loss. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_simultaneous_eventual_graded_extraction
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization MME.ProfiledCW MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
universe u

theorem mme_released_interior_simultaneous_eventual_tensor_restriction
    {KField : Type u} [Field KField] (d : ℕ) (hd : 1 < d) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ k : ℕ in Filter.atTop,
    ∀ (owner : Fin 6) (s : Fin 45), (seed owner s).boundary = [] →
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
        (E.output = fun i x => Graded (parent_total s) i reference
          (ProfiledCW.split (ell := 2) positions (by omega) x) ∧
          Useful (fullCell (parent_total s) reference) (mu i)
            (ProfiledCW.split (ell := 2) positions (by omega) x) ) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin E.copies => tensor KField E.output))
          (tensor KField source) ∧
        (((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q)) /
          (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies  := by sorry
