-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarRAMStep_eq_execInstr
-- name    : WilliamsonShmoys.planarRAMStep_eq_execInstr
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T11:45:51.203861+00:00
-- url     : https://prove2.me/theorems/9f94b4ea-cf54-45d1-8ca1-229b491474af
-- title:
--   One RAM step executes the instruction at the program counter
-- statement:
--   If the instruction of program $p$ at the program counter of state $s$ is `ins`, then
--
--   $$\mathrm{step}_p(s)=\mathrm{exec}(\mathrm{ins},s).$$
--
--   This turns reasoning about runs into reasoning about explicit instruction effects, one instruction at a time.
--
--   **Formalization Note.** Uses `execInstr` and `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction

theorem WilliamsonShmoys.planarRAMStep_eq_execInstr (p : List PlanarRAMInstruction) (s : PlanarRAMState) (ins : PlanarRAMInstruction)
    (h : p[s.pc]? = some ins) : planarRAMStep p s = execInstr ins s := by sorry
