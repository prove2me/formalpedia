-- Prove2me | Theorems.Thm_mme_entropy_penalty_coordinate_equiv
-- name    : mme_entropy_penalty_coordinate_equiv
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:42:35.296041+00:00
-- url     : https://prove2.me/theorems/5dde3a5b-7c9e-4280-a661-9a98d8713abd
-- title:
--   Physical mode permutations preserve entropy penalties
-- statement:
--   Relabeling the physical coordinates transports the feasible same-marginal distributions and preserves their entropy values, hence the maximum-entropy penalty. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_recursive_split_coordinate_data
open scoped BigOperators
open MME.RecursiveThinSplit

theorem mme_entropy_penalty_coordinate_equiv
    {half : ℕ} (parent : Fin 3 → ℕ) (p : Equiv.Perm (Fin 3))
    (alpha : Split half parent → ℝ) :
    entropyPenalty (fun c => alpha ((coordinateEquiv parent p).symm c)) =
      entropyPenalty alpha := by sorry
