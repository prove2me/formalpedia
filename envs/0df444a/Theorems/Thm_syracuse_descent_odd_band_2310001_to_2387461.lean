-- Prove2me | Theorems.Thm_syracuse_descent_odd_band_2310001_to_2387461
-- name    : syracuse_descent_odd_band_2310001_to_2387461
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-02T18:52:28.473668+00:00
-- url     : https://prove2.me/theorems/3b321bb3-a21b-451c-a7e9-da9d072f1534
-- title:
--   Strict Syracuse descent within 512 steps for odd inputs 2310001 through 2387461
-- statement:
--   Let $T(n)$ be the odd part of $3n+1$, the accelerated Syracuse map. For a natural index $i<38731$, put $n=2310001+2i$. Then
--
--   $$\exists t\in\mathbb N,\qquad t\le512\quad\text{and}\quad T^t(n)<n.$$
--
--   Equivalently, every odd starting value from $2310001$ through $2387461$, inclusive, has a strict descent within512 accelerated steps. The bound is a time to become smaller than the starting value, not a bound on total time to reach one. This is a finite descent assertion, not an unbounded trajectory-convergence theorem or a completed cycle-exclusion baseline.
-- source:
--   Credits the exact checker and soundness proofs in the existing workspace Solutions/CollatzFiniteDescent.lean and Solutions/CollatzFiniteDescentChunks.lean, and the eight historical certificates Solutions/CollatzFiniteDescentExtensionChunk000.lean through007.lean. Their original indexed formula is1883433+2j, starting at j212015 with eight5000-index chunks. The public band uses j213284+i, skipping1269 original indices, and has38731 inputs through j252014. Historical certificate report: C:/Users/jason/prove2me_workspace/certificates/finite_descent_extended_band/certificates-report.json . Historical checking and104.945-second summed chunk timing are provenance, not new public acceptance or a remote300-second runtime guarantee. This is a distinct first finite-band block, not a renamed retry of the timed-out syracuse_no_cycle_below_2786502 proof; that baseline remains Open in the saved canonical readback. Only the canonical SyracuseStep definition is imported, with no public theorem support assumption.

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_descent_odd_band_2310001_to_2387461 (i : ℕ) (hi : i < 38731) :
    ∃ t ≤ 512,
      syracuseStep^[t] (2310001 + 2 * i) < 2310001 + 2 * i := by sorry
