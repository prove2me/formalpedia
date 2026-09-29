-- Prove2me | Theorems.Thm_mme_released_global_parent_source_restricts_common_window
-- name    : mme_released_global_parent_source_restricts_common_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T08:08:09.499832+00:00
-- url     : https://prove2.me/theorems/a91db1a6-2f05-443e-8c7f-91a27655accb
-- title:
--   Local parent sources restrict from a common global histogram window
-- statement:
--   For every positive released global recipe weight, the local parent source restricts from the normalized global cell at the same nonnegative histogram tolerance. The proof checks that all released global alpha weights are at most the denominator and uses the exact normalized-cell/source bridge plus allowed-set inclusion. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_global_normalized_cell_eq_parent_source
import Theorems.Thm_mme_basis_all_allowed_subtensor_mono
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
universe u

theorem mme_released_global_parent_source_restricts_common_window
    {K : Type u} [Field K] (owner : Fin 6) (s : Fin 45)
    (ha0 : 0 < alpha owner s) (t : ℕ) (ht : 0 < t) (eps : ℝ) (heps : 0 ≤ eps) :
    let L := t * coarseCounts owner (shapeEquiv s)
    TensorObj.Restrict
      (ProfiledCW.tensor K (fun i (x : ProfiledCW.FineWord (L * 4)) =>
      (∀ p : Fin L,
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
          ((shapeEquiv s).val i).val) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin L //
          ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / L -
          ((((jointRows owner s).map
            (fun a => if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ)^4| ≤ eps))
      ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L)
      (fun i x =>
        (∀ r, grade (label 5 3 L (Equiv.refl _) x r) = ((shapeEquiv s).val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / L -
          ((blocks t : ℝ) / L) * (profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          ((blocks t : ℝ) / L) * (eps))) := by sorry
