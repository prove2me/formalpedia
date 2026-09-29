-- Prove2me | Theorems.Thm_mme_released_global_normalized_cell_eq_parent_source
-- name    : mme_released_global_normalized_cell_eq_parent_source
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T03:14:28.742777+00:00
-- url     : https://prove2.me/theorems/56490488-b328-4c27-bbcc-ac497ca95e14
-- title:
--   Every positive released global cell equals its conditioned parent source
-- statement:
--   For every owner and positive coarse weight, the actual normalized cell tensor at the appropriately scaled global tolerance equals the flat graded histogram tensor centered on that owner and shape’s released conditional row marginals.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Definitions.Def_mme_released_global_frame_data
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_normalized_cell_eq_parent_source
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
            (denominator : ℝ)^4| ≤ eps) := by sorry
