-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarRAMRun_of_halt
-- name    : WilliamsonShmoys.planarRAMRun_of_halt
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:02:56.694629+00:00
-- url     : https://prove2.me/theorems/bc67bb5e-a716-42e3-a5eb-20b0636701c0
-- title:
--   Halted states are stable
-- statement:
--   If the instruction at the program counter of $s$ is `halt`, then for every $t$,
--
--   $$\mathrm{run}_p(s,t)=s.$$
--
--   So once a program has halted, running longer changes nothing; this lets a time bound be padded freely.
--
--   **Formalization Note.** $\mathrm{run}_p(s,t)$ is `planarRAMRun p s t`, the $t$-fold iterate of `planarRAMStep p`; triples are `RAMSpec` from `Def_WilliamsonShmoys_RAMSpec`.
-- source:
--   Program-logic infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSpec

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarRAMRun_of_halt (program : List PlanarRAMInstruction) (s : PlanarRAMState)
    (h : program[s.pc]? = some PlanarRAMInstruction.halt) (t : ℕ) :
    planarRAMRun program s t = s := by sorry
