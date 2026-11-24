-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_real_spread_fragment
-- name    : WilliamsonShmoys.ram_real_spread_fragment
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T15:28:54.212518+00:00
-- url     : https://prove2.me/theorems/b6cbf3f2-5e91-49ff-bf1b-2b08498d5936
-- title:
--   RAM fragment relocating the vertex weights to even cells
-- statement:
--   Let a program $p$ contain, at position $\mathrm{base}$, the 16-instruction fragment that relocates the real input (the vertex weights) to even cells. Started at $\mathrm{base}$ with $n$ in natural cell 0, $1$ in cell 11 and $0$ in cell 12, after exactly $5+(7(n-1)+1)+4$ operations the program counter is $\mathrm{base}+16$ and, for every $c<n$,
--
--   $$\text{real cell }(2c+32)=\text{original real cell }c.$$
--
--   Moreover real cells $0$ and $2n+1$ are $0$, every other real cell outside the targets and cell 32 is unchanged, and only the natural scratch cells $2,3,6,7$ change.
--
--   Real values can only be moved through a fixed real register, and every fixed real cell holds input data. The fragment therefore first parks real cell 0 in the odd cell $2n+1$, which is neither a later source nor a target. It then copies $c=n-1,\dots,1$ downwards using real cell 0 as the register, restores cell 0's value to its target 32, and finally clears both auxiliary cells, so that later the sandboxed solver sees zeros there.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction

theorem WilliamsonShmoys.ram_real_spread_fragment (p : List PlanarRAMInstruction) (base : ℕ)
    (hcode : CodeAt p base
      [natAdd 2 0 12, natConst 6 32, natAdd 3 0 0, natAdd 3 3 11, realStore 3 0, natBranch 2 11 (base + 12) (base + 6), natSub 2 2 11, natAdd 7 2 2, natAdd 7 7 6, realLoad 0 2, realStore 7 0, jump (base + 5), realLoad 0 3, realStore 6 0, realSub 0 0 0, realStore 3 0]) (s : PlanarRAMState) (hpc : s.pc = base) (h11 : s.natMem 11 = 1)
    (h12 : s.natMem 12 = 0) :
    let n := s.natMem 0
    let s' := planarRAMRun p s (5 + (7 * (n - 1) + 1) + 4)
    s'.pc = base + 16 ∧
      (∀ c, c < n → s'.realMem (2 * c + 32) = s.realMem c) ∧
      s'.realMem 0 = 0 ∧ s'.realMem (2 * n + 1) = 0 ∧
      (∀ a, a ≠ 0 → a ≠ 32 → a ≠ 2 * n + 1 → (∀ c, c < n → a ≠ 2 * c + 32) →
        s'.realMem a = s.realMem a) ∧
      (∀ a, a ≠ 2 → a ≠ 3 → a ≠ 6 → a ≠ 7 → s'.natMem a = s.natMem a) := by sorry
