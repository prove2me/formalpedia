-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.maxLik_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T07:12:47.001+00:00
-- url     : https://prove2.me/submissions/2c4c8444-153c-4af6-86db-b8261e6852bd

import Definitions.Def_MachineLearning_UniversalRedundancy_Core

open UniversalRedundancy

open UniversalRedundancy in
/-- **The maximum likelihood of a message is nonnegative.** -/
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Nonempty Θ] (x : X) :
    0 ≤ S.maxLik x :=
  by exact Real.iSup_nonneg (fun θ => S.nonneg θ x)
