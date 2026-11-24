-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarRAMRun_succ_right
-- name    : WilliamsonShmoys.planarRAMRun_succ_right
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:02:56.913843+00:00
-- url     : https://prove2.me/theorems/79037877-3894-4fc4-8b95-aee40444fdcb
-- title:
--   Last-step decomposition of a run
-- statement:
--   For every program $p$, state $s$ and $t$,
--
--   $$\mathrm{run}_p(s,t+1)=\mathrm{step}_p(\mathrm{run}_p(s,t)).$$
--
--   It lets one argue about a run by looking at its final operation.
--
--   **Formalization Note.** $\mathrm{run}_p(s,t)$ is `planarRAMRun p s t`, the $t$-fold iterate of `planarRAMStep p`; triples are `RAMSpec` from `Def_WilliamsonShmoys_RAMSpec`.
-- source:
--   Program-logic infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSpec

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarRAMRun_succ_right (program : List PlanarRAMInstruction) (s : PlanarRAMState) (t : ℕ) :
    planarRAMRun program s (t + 1) = planarRAMStep program (planarRAMRun program s t) := by sorry
