-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_zero_odd_cells
-- name    : WilliamsonShmoys.ram_zero_odd_cells
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T06:02:46.823368+00:00
-- url     : https://prove2.me/theorems/d3c03075-ef98-4403-aada-45bd1749bff7
-- title:
--   RAM loop clearing the odd sandbox cells
-- statement:
--   This loop clears the odd memory cells before a sandboxed subprogram is started. In the odd-cell sandbox (`SandboxedOddAt`, `SandboxOddRel`), the subprogram's cell $a$ lives in the host's odd cell $2a+1$. The host must therefore make the odd cells hold exactly the subprogram's initial memory, which is zero outside its input.
--
--   Let a program $p$ contain, at position $z$, the 9-instruction loop. It uses only the even cells $0$, $2$, $4$, $6$ (pointer, bound, step $2$, zero) and the even real cell $0$. If cell $2$ holds $2K+1$, the program reaches $z+9$ within $5K+5$ operations, and for every $i<K$
--
--   $$\mathrm{nat}'(2i+1)=0,\qquad \mathrm{real}'(2i+1)=0 .$$
--
--   All natural cells other than $0,4,6$ and the cleared odd cells are unchanged, and so are all real cells other than $0$ and the cleared odd cells.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (subroutine call)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_zero_odd_cells (p : List PlanarRAMInstruction) (z : ℕ)
    (hcode : CodeAt p z
    [natConst 0 1,
      natConst 4 2,
      natConst 6 0,
      realZero 0,
      natBranch 2 0 (z + 9) (z + 5),
      natStore 0 6,
      realStore 0 0,
      natAdd 0 0 4,
      jump (z + 4)])
    (K : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h2 : M 2 = 2 * K + 1) :
    ∃ τ, τ ≤ 5 * K + 5 ∧ (planarRAMRun p ⟨z, M, R⟩ τ).pc = z + 9 ∧
      (∀ i, i < K → (planarRAMRun p ⟨z, M, R⟩ τ).natMem (2 * i + 1) = 0 ∧ (planarRAMRun p ⟨z, M, R⟩ τ).realMem (2 * i + 1) = 0) ∧
      (∀ a, a ≠ 0 → a ≠ 4 → a ≠ 6 → (∀ i, i < K → a ≠ 2 * i + 1) → (planarRAMRun p ⟨z, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≠ 0 → (∀ i, i < K → a ≠ 2 * i + 1) → (planarRAMRun p ⟨z, M, R⟩ τ).realMem a = R a) := by sorry
