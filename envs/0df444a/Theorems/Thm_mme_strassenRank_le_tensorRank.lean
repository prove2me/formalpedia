-- Prove2me | Theorems.Thm_mme_strassenRank_le_tensorRank
-- name    : mme_strassenRank_le_tensorRank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-28T14:37:16.984617+00:00
-- url     : https://prove2.me/theorems/54e8a838-e575-44f4-a898-20035a17ced8
-- statement:
--   **Decomposition ⇒ restriction:** `strassenRank T ≤ tensorRank T`. If $T=\sum_{j<r} v_{j,1}\otimes\cdots\otimes v_{j,d}$ is an $r$-term pure-tensor decomposition (a `tensorRank` witness), the linear maps $e_j\mapsto v_{j,i}$ send the diagonal unit $I_r$ to $T$, witnessing `Restrict T I_r`. So every `tensorRank` witness is a `strassenRank` witness, giving `strassenRank T ≤ tensorRank T`.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Definitions.Def_mme_omega
import Definitions.Def_mme_omega_strassen
universe u
open MME

theorem mme_strassenRank_le_tensorRank {K : Type u} [Field K] {d : ℕ}
    {V : Fin d → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (T : PiTensorProduct K V) :
    strassenRank T ≤ tensorRank T := by sorry
