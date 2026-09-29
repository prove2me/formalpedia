-- Prove2me | Theorems.Thm_KServer_chunk_system_f_base
-- name    : KServer.chunk_system_f_base
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T09:55:18.869119+00:00
-- url     : https://prove2.me/theorems/d992b5cd-7c92-4381-9776-db0957392e19
-- title:
--   The base case: a filtered chunk system on the path
-- statement:
--   **The base case of BCR's Lemma 6, in the filtered form**: on the path of $\beta + 1$ equally spaced points (with $s = 0$, $t = \beta$, so $d(s,t) = \beta$), whenever $\alpha w^2 \le 1$ there is a deterministic filtered chunk system with $m = \beta$ chunks: after an initial pinning request $\{0\}$, the $i$-th chunk is the single request $\{i\}$, of size $1 \in [\tfrac12, \tfrac32]$, with trivial filtration. The total size $\beta$ dominates $\alpha w^2\beta$, and $m = \beta \ge \lceil \alpha\beta w^2\rceil$; the conditional cost bound holds with escape price $2\beta$ because the previous singleton request pins the evader one step away.
--
--   This is the same statement as `chunk_system_base` transported to the filtered package `KServer_chunk_system_f`, which is the form consumed by the combining and subchunk steps of the induction.
--
--   ## Formalization note
--
--   The filtration is constant (`hist ≡ 0`): the system is deterministic.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 6 (base case).

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_chunk_system
import Definitions.Def_KServer_chunk_system_f

namespace KServer

theorem chunk_system_f_base (β : ℕ) (hβ : 1 ≤ β) (α : ℝ) (hα0 : 0 ≤ α) (w : ℕ)
    (hw : α * (w : ℝ) ^ 2 ≤ 1) :
    letI := pathMetric β
    dist (0 : Fin (β + 1)) (Fin.last β) = β ∧
    Nonempty (ChunkSystemF (Fin (β + 1)) 0 (Fin.last β)
      (1 / 2) (3 / 2) (α * (w : ℝ) ^ 2 * β) (2 * β) ⌈α * β * (w : ℝ) ^ 2⌉₊) := by sorry

end KServer
