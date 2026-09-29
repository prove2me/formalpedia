-- Prove2me | Theorems.Thm_mme_released_global_joint_counts_valid
-- name    : mme_released_global_joint_counts_valid
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T11:20:58.643985+00:00
-- url     : https://prove2.me/theorems/2ffcffde-c3d0-4a59-a951-1c169b896ca7
-- title:
--   Exact six-orientation global candidate: masses and supported grades
-- statement:
--   The explicit six-orientation candidate has normalized coarse masses, conditional joint mass 10^48 in every one of its 270 cells, and the prescribed complete-word grade in every positive atom. The shape and word alphabets have cardinalities 45 and 81, and all six orientation maps are permutations with consistent coarse reindexing.
-- source:
--   Concrete global profile obligations for More Asymmetry Theorem 5.3, https://arxiv.org/html/2404.16349v2#S5 . This is an explicit rational candidate reconstructed from the released primitive seed; the numerical rate inequalities and whole-interface continuation remain separate obligations.

import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000
universe u

theorem mme_released_global_joint_counts_valid :
    (∀ owner : Fin 6, ∑ s : Fin 45, alpha owner s = denominator) ∧
    (∀ owner : Fin 6, ∀ s : Fin 45,
      ((jointRows owner s).map Prod.snd).sum = denominator^4 ∧
      ∀ a ∈ jointRows owner s, ∀ i : Fin 3,
        RecursiveYZ.CWCells.grade (atom a.1 i) = ((shape s).val i).val) ∧
    Fintype.card Shape = 45 ∧ Fintype.card Word = 81 ∧
    (∀ owner : Fin 6, Function.Bijective (roles owner)) ∧
    (∀ (owner : Fin 6) (s : Fin 45) (i : Fin 3),
      (shape (sourceIndex owner s)).val (roles owner i) = (shape s).val i) := by
  sorry
