-- Prove2me | Theorems.Thm_KServer_chunk_system_b_base
-- name    : KServer.chunk_system_b_base
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T10:07:26.537602+00:00
-- url     : https://prove2.me/theorems/26d0df2f-4cae-44fe-a9ca-04a77b30622b
-- title:
--   The base case: a chunk system with online escapes on the path
-- statement:
--   **The base case of BCR's Lemma 6 in the final (online-escape) package**: on the path of $\beta+1$ equally spaced points, whenever $\alpha w^2 \le 1$ there is a deterministic chunk system with online-escape conditional cost bounds: $m = \beta$ chunks of size $1$, an initial pinning request $\{0\}$, singleton requests $\{i\}$, trivial filtration, unit weights. The online-escape bounds follow from the already-established offline-escape bounds pointwise (`escapeCost_le_bailCost`).
--
--   Same content as `chunk_system_base` / `chunk_system_f_base`, in the package consumed by the combining and subchunk steps.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 6 (base case).

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_chunk_system
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem chunk_system_b_base (β : ℕ) (hβ : 1 ≤ β) (α : ℝ) (hα0 : 0 ≤ α) (w : ℕ)
    (hw : α * (w : ℝ) ^ 2 ≤ 1) :
    letI := pathMetric β
    dist (0 : Fin (β + 1)) (Fin.last β) = β ∧
    Nonempty (ChunkSystemB (Fin (β + 1)) 0 (Fin.last β)
      (1 / 2) (3 / 2) (α * (w : ℝ) ^ 2 * β) (2 * β) ⌈α * β * (w : ℝ) ^ 2⌉₊) := by sorry

end KServer
