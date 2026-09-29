-- Prove2me | Theorems.Thm_KServer_chunk_system_transport
-- name    : KServer.chunk_system_transport
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T13:08:04.866161+00:00
-- url     : https://prove2.me/theorems/aab5eb1f-22c1-4f71-a220-da16c42b047e
-- title:
--   Transport of chunk systems along marked isometries
-- statement:
--   **Transport of chunk systems along marked isometries.** If \(C\) is a chunk system with online escapes on \(X\) with marked points \(s, t\), and \(\varphi : X \to Y\) is a distance-preserving bijection, then pushing every request set forward along \(\varphi\) yields a chunk system on \(Y\) with marked points \(\varphi(s), \varphi(t)\) and identical outcome space, weights, filtration, sizes, escape price and expected total. The conditional cost bound transfers by pulling a \(Y\)-evader and its online bail rule back along \(\varphi^{-1}\) (costs, bail times and escape semantics are preserved verbatim), and the offline optimum is preserved because serving paths correspond bijectively. In the BCR induction this places the inductively constructed systems into the isometric copies of the level spaces in either orientation: a system for \((M, t, s)\) is transported onto a reversed copy without requiring any reflection symmetry of \(M\) itself.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 4 (orientation handling).

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem chunk_system_transport {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s t : X} {cLo cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo)
    (φ : X ≃ Y) (hφ : ∀ a b : X, dist (φ a) (φ b) = dist a b) :
    Nonempty (ChunkSystemB Y (φ s) (φ t) cLo cHi total price mLo) := by sorry

end KServer
