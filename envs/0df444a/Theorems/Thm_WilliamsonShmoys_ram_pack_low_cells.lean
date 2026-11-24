-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_pack_low_cells
-- name    : WilliamsonShmoys.ram_pack_low_cells
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T11:46:00.471219+00:00
-- url     : https://prove2.me/theorems/9b85a633-3230-4269-a768-52d681b533fa
-- title:
--   RAM fragment packing cells 2–7 into cell 1
-- statement:
--   Let the program $p$ contain, at position $\mathrm{base}$, the 12 instructions that six times double cell 1 and then add cell $c$, for $c=2,\dots,7$. Started at $\mathrm{base}$ from a state with natural memory $M$, after exactly 12 operations the program counter is $\mathrm{base}+12$, every cell other than cell 1 is unchanged, and cell 1 holds
--
--   $$64\,M_1+32\,M_2+16\,M_3+8\,M_4+4\,M_5+2\,M_6+M_7.$$
--
--   In the mission's input layout, cell 1 holds the accuracy parameter $k$ and cells $2,\dots,7$ hold adjacency bits (or zeros), all at most $1$. So this fragment frees six fixed cells for use as working registers without losing information, a prerequisite for any loop in a host program, whose input otherwise fills every fixed address.
--
--   **Formalization Note.** Uses `execInstr` and `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction

theorem WilliamsonShmoys.ram_pack_low_cells (p : List PlanarRAMInstruction) (base : ℕ) (s : PlanarRAMState)
    (hcode : CodeAt p base
      [natAdd 1 1 1, natAdd 1 1 2, natAdd 1 1 1, natAdd 1 1 3, natAdd 1 1 1, natAdd 1 1 4, natAdd 1 1 1, natAdd 1 1 5, natAdd 1 1 1, natAdd 1 1 6, natAdd 1 1 1, natAdd 1 1 7])
    (hpc : s.pc = base) :
    planarRAMRun p s 12 =
      { pc := base + 12,
        natMem := Function.update s.natMem 1
          (64 * s.natMem 1 + 32 * s.natMem 2 + 16 * s.natMem 3 + 8 * s.natMem 4 +
            4 * s.natMem 5 + 2 * s.natMem 6 + s.natMem 7),
        realMem := s.realMem } := by sorry
