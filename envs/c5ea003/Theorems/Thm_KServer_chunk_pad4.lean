-- Prove2me | Theorems.Thm_KServer_chunk_pad4
-- name    : KServer.chunk_pad4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-02T00:13:14.154218+00:00
-- url     : https://prove2.me/theorems/edf7cc94-43cc-4655-815b-4cbc58b03beb
-- title:
--   Chunk padding with prophecy pass-through
-- statement:
--   Chunk padding with the full recursion invariant bundle. Identical to chunk_pad3 (replace each empty chunk by a single repeat of the last consumed request, keeping the sample space, weights, filtration, sizes, chunk count, expected total, variance, L1-sturdiness and below-floor counts, and making every chunk nonempty), with one additional hypothesis and conclusion: the partitioned prophecy energy bound ProphecyBound PE passes through with the same constant, since the padding changes only the request lists and none of the probabilistic data (weights, filtration, sizes) that the prophecy energy depends on.
-- source:
--   Bartal-Chrobak-Rasala lower bound program: padding with prophecy energy

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_chunk_adjust
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_chunk_var
import Definitions.Def_KServer_prophecy

namespace KServer

theorem chunk_pad4 {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ}
    {mL : ℕ} (C : ChunkSystemB X s t 0 cB T pe mL)
    {V D B flo PE : ℝ} {n₀ : ℕ}
    (hpe0 : 0 ≤ pe)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hst : C.SturdyL1 n₀ D)
    (hbad : ∀ n ≤ n₀, ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B)
    (hPPE : C.ProphecyBound PE) :
    ∃ C' : ChunkSystemB X s t 0 cB T pe mL,
      C'.m = C.m ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.SturdyL1 n₀ D ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B) ∧
      C'.ProphecyBound PE := by
  sorry

end KServer
