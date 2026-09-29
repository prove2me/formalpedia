-- Prove2me | Theorems.Thm_mme_tensorRank_le_strassenRank
-- name    : mme_tensorRank_le_strassenRank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-28T14:37:08.44966+00:00
-- url     : https://prove2.me/theorems/1bc796fa-e7f9-4a88-b3ee-abe35c55f0ac
-- statement:
--   **Restriction ⇒ decomposition:** `tensorRank T ≤ strassenRank T`. If `T` is a restriction of the diagonal unit tensor `I_r` (a `strassenRank` witness) — i.e. linear maps $f_i$ send $I_r$ to $T$ — then expanding $I_r=\sum_j e_j\otimes\cdots\otimes e_j$ gives $T=\sum_{j<r} f_1(e_j)\otimes\cdots\otimes f_d(e_j)$, an $r$-term decomposition. So every `strassenRank` witness is a `tensorRank` witness, giving `tensorRank T ≤ strassenRank T`.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Definitions.Def_mme_omega
import Definitions.Def_mme_omega_strassen
universe u
open MME

theorem mme_tensorRank_le_strassenRank {K : Type u} [Field K] {d : ℕ}
    {V : Fin d → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (T : PiTensorProduct K V) :
    tensorRank T ≤ strassenRank T := by sorry
