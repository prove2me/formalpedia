-- Prove2me | Definitions.Def_KServer_evader_bail
-- name    : KServer_evader_bail
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T10:05:57.20725+00:00
-- url     : https://prove2.me/theorems/20ae8ae3-ebb7-49ac-a70b-c8f7adc3f3e1
-- title:
--   Online escape rules for the evader
-- statement:
--   The **online escape semantics** for metrical service systems: a bail rule is a predicate on request histories; serving a chunk under a bail rule with escape price $p$, the evader checks the rule before each request and, the first time it fires, pays $p$ and stops (`bailCost`, via the first firing position `bailTime`). Because the rule sees only the requests so far, this models the online escape option of Bubeck–Coester–Rabani's escape price relaxation faithfully — in particular, the decision may depend on the evader's own (history-determined) position.
--
--   The offline-optimal escape cost `escapeCost` (minimum over all bail positions) lower-bounds `bailCost` for every rule (`escapeCost_le_bailCost`), so lower bounds proved against offline escapes transfer to online ones.
--
--   ## Role
--
--   Chunk-combining (BCR Lemma 10) requires escape decisions to be adapted: the charging argument partitions outcomes by whether the escape has already happened before a given subchunk, which must be measurable at that subchunk's start time. The offline minimum does not compose across subchunks, so the induction package `KServer_chunk_system_b` states its conditional cost bounds against `bailCost`.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 2 (escape price relaxation), online form.

import Mathlib
import Definitions.Def_KServer_evader

namespace KServer

/-- The first within-chunk position at which the history-dependent bail
predicate fires, if any: position `q` means bailing instead of serving the
`q`-th request of the chunk. -/
def bailTime {X : Type*} (bail : List (Set X) → Bool) (h χ : List (Set X)) : Option ℕ :=
  (List.range χ.length).find? (fun q => bail (h ++ χ.take q))

/-- The cost of the evader `E` on the chunk `χ` served after the history `h`,
under the **online escape rule** `bail` with escape price `p`: before serving
each request of the chunk, if `bail` fires on the current history the evader
pays `p` and stops (paying nothing thereafter); otherwise it serves the whole
chunk. Because `bail` sees only the requests so far, this models an online
escape decision; the pointwise minimum `escapeCost` lower-bounds it. -/
noncomputable def EvaderAlgorithm.bailCost {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h χ : List (Set X)) (p : ℝ) : ℝ :=
  match bailTime bail h χ with
  | some q => E.costOn h (χ.take q) + p
  | none => E.costOn h χ

/-- The offline-optimal escape cost lower-bounds every online escape rule. -/
theorem escapeCost_le_bailCost {X : Type*} [MetricSpace X]
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h χ : List (Set X)) (p : ℝ) :
    E.escapeCost h χ p ≤ E.bailCost bail h χ p := by
  unfold EvaderAlgorithm.bailCost
  rcases hq : bailTime bail h χ with - | q
  · -- never bails: the full-service branch of the minimum
    have hmem : χ.length ∈ Finset.range (χ.length + 1) := by
      simp
    have h1 := Finset.inf'_le
      (fun t => if t = χ.length then E.costOn h χ else E.costOn h (χ.take t) + p) hmem
    unfold EvaderAlgorithm.escapeCost
    rw [if_pos rfl] at h1
    exact h1
  · -- bails at `q < χ.length`
    have hqlt : q < χ.length := by
      have hmem := List.mem_of_find?_eq_some hq
      exact List.mem_range.mp hmem
    have hmem : q ∈ Finset.range (χ.length + 1) := by
      simp only [Finset.mem_range]
      omega
    have h1 := Finset.inf'_le
      (fun t => if t = χ.length then E.costOn h χ else E.costOn h (χ.take t) + p) hmem
    unfold EvaderAlgorithm.escapeCost
    rw [if_neg (by omega)] at h1
    exact h1

end KServer


