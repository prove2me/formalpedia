-- Prove2me | solution 2 for CayleyCensus.CensusEquiv_sq_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:47:47.72119+00:00
-- url     : https://prove2.me/submissions/8bc5c719-dbdc-44ef-aba0-46a20de6c203

import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments
import Definitions.Def_MachineLearning_CayleyCensusGraphSymmetry

open CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

namespace CayleyCensus

omit [Fintype G] [DecidableEq G] in
theorem solution {S : Finset G} {g h : G} (hgh : CensusEquiv S g h) :
    g ^ 2 = 1 ↔ h ^ 2 = 1 := by
  induction hgh with
  | refl => exact Iff.rfl
  | @inv h _ ih =>
      refine ih.trans ⟨fun hh => ?_, fun hh => ?_⟩
      · rw [inv_pow, hh, inv_one]
      · rwa [inv_pow, inv_eq_one] at hh
  | @aut h σ _ _ ih =>
      refine ih.trans ⟨fun hh => ?_, fun hh => ?_⟩
      · rw [← map_pow, hh, map_one]
      · rw [← map_pow] at hh
        exact (map_eq_one_iff σ σ.injective).mp hh

end CayleyCensus

open CayleyCensus

omit [Fintype G] [DecidableEq G] in
theorem solution {S : Finset G} {g h : G} (hgh : CensusEquiv S g h) :
    g ^ 2 = 1 ↔ h ^ 2 = 1 :=
  CayleyCensus.solution hgh

#print axioms solution
