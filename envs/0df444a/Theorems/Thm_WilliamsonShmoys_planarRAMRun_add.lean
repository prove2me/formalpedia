-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarRAMRun_add
-- name    : WilliamsonShmoys.planarRAMRun_add
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:02:58.903559+00:00
-- url     : https://prove2.me/theorems/4dfd8c1e-f4fb-4e85-aa70-642df144ee8a
-- title:
--   Run additivity
-- statement:
--   For every program $p$, state $s$ and $a,b\in\mathbb N$,
--
--   $$\mathrm{run}_p(s,a+b)=\mathrm{run}_p(\mathrm{run}_p(s,a),b).$$
--
--   This is the basic fact used to compose consecutive code fragments.
--
--   **Formalization Note.** $\mathrm{run}_p(s,t)$ is `planarRAMRun p s t`, the $t$-fold iterate of `planarRAMStep p`; triples are `RAMSpec` from `Def_WilliamsonShmoys_RAMSpec`.
-- source:
--   Program-logic infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSpec

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarRAMRun_add (program : List PlanarRAMInstruction) (s : PlanarRAMState) (a b : ℕ) :
    planarRAMRun program s (a + b) = planarRAMRun program (planarRAMRun program s a) b := by sorry
