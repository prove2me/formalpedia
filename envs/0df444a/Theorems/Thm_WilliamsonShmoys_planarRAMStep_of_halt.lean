-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarRAMStep_of_halt
-- name    : WilliamsonShmoys.planarRAMStep_of_halt
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:02:57.86972+00:00
-- url     : https://prove2.me/theorems/36314199-0b29-4ed7-8011-daf6da2dece8
-- title:
--   A halt instruction is a fixed point of the step
-- statement:
--   If the instruction at the program counter of $s$ is `halt`, then $\mathrm{step}_p(s)=s$.
--
--   Halting therefore freezes the machine state.
--
--   **Formalization Note.** $\mathrm{run}_p(s,t)$ is `planarRAMRun p s t`, the $t$-fold iterate of `planarRAMStep p`; triples are `RAMSpec` from `Def_WilliamsonShmoys_RAMSpec`.
-- source:
--   Program-logic infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSpec

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarRAMStep_of_halt (program : List PlanarRAMInstruction) (s : PlanarRAMState)
    (h : program[s.pc]? = some PlanarRAMInstruction.halt) :
    planarRAMStep program s = s := by sorry
