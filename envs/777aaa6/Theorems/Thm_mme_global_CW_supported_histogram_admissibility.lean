-- Prove2me | Theorems.Thm_mme_global_CW_supported_histogram_admissibility
-- name    : mme_global_CW_supported_histogram_admissibility
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T10:25:07.674929+00:00
-- url     : https://prove2.me/theorems/47213066-e374-4e8f-9146-271d137db274
-- title:
--   Supported global words yield admissible exact histograms
-- statement:
--   For unpaired global positions, any supported graded triple has the prescribed coarse cell masses, supported complete-word grades, and all three boundary-complement histogram identities.
-- source:
--   Finite global realization for More Asymmetry Theorem 5.3, https://arxiv.org/html/2404.16349v2#S5 . This constructs the global window extraction needed by the joint finite-witness architecture; released profile and numerical instantiation remain open.

import Definitions.Def_mme_global_CW_histogram_frame
import Definitions.Def_mme_global_CW_entropy_data
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RegionRate MME.RecursiveYZ MME.GlobalCW MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_supported_histogram_admissibility {ell M : ℕ} (D : HistogramFrame ell M)
    (x : Fin 3 → Place D.n → CompleteWord ell)
    (hgrade : ∀ i, Graded i D.reference (x i))
    (hsupport : ∀ p r, (x 0 p r).val + (x 1 p r).val + (x 2 p r).val = 2) :
    D.Admissible (fun i ↦ count (cell D.reference) (x i)) := by
  sorry
