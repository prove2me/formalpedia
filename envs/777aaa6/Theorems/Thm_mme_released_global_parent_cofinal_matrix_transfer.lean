-- Prove2me | Theorems.Thm_mme_released_global_parent_cofinal_matrix_transfer
-- name    : mme_released_global_parent_cofinal_matrix_transfer
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T03:14:10.150852+00:00
-- url     : https://prove2.me/theorems/c5682bbf-e6be-4986-92fb-24c46d1cf1f2
-- title:
--   Cofinal parent matrix extractions transfer to released global cells
-- statement:
--   Cofinal matrix-family extractions from a released conditioned parent source, at replications divisible by its coarse weight, give cofinal extractions from the actual normalized global cell. The matrix family, positivity of its number of copies, and exponential weight bound are preserved exactly.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_released_global_frame_data
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_parent_cofinal_matrix_transfer
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
        Real.exp (rate (alpha owner s * t)) ≤ ∑ v, ((a v * b v * c v : ℕ) : ℝ)^tau := by sorry
