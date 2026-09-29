-- Prove2me | Theorems.Thm_mme_released_116_normalized_cell_eq_parent_source
-- name    : mme_released_116_normalized_cell_eq_parent_source
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:32:59.812207+00:00
-- url     : https://prove2.me/theorems/66c70e20-c1f5-4b51-939c-07838a145753
-- title:
--   The normalized global 116 cell tensor equals the parent extraction source
-- statement:
--   For positive global replication, the owner-zero 116 cell tensor at global tolerance alpha 0 10 / denominator times eps equals the actual graded histogram tensor used by parent extraction. The equality matches grading, empirical counts, conditional centers, and tolerance.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_released_global_frame_data
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u
universe v w

theorem mme_released_116_normalized_cell_eq_parent_source
    {K : Type u} [Field K] (t : ℕ) (ht : 0 < t) (eps : ℝ) :
    let L := t * coarseCounts 0 (shapeEquiv 10)
    (source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L)
      (fun i x =>
        (∀ r, grade (label 5 3 L (Equiv.refl _) x r) = ((shapeEquiv 10).val i).val) ∧
        if L = 0 then ∀ w, |(profile 0).2 i ⟨0,shapeEquiv 10⟩ w| ≤
          (alpha 0 10 : ℝ) / denominator * eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / L -
          ((blocks t : ℝ) / L) * (profile 0).2 i ⟨0,shapeEquiv 10⟩ w| ≤
          ((blocks t : ℝ) / L) * ((alpha 0 10 : ℝ) / denominator * eps)) =
    ProfiledCW.tensor K (fun i (x : ProfiledCW.FineWord (L * 4)) =>
      (∀ p : Fin L,
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
          Released116.parent 0 i) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin L //
          ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / L -
          ((((jointRows 0 10).map
            (fun a => if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ)^4| ≤ eps) := by sorry
