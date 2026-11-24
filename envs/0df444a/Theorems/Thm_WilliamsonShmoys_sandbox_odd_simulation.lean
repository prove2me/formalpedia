-- Prove2me | Theorems.Thm_WilliamsonShmoys_sandbox_odd_simulation
-- name    : WilliamsonShmoys.sandbox_odd_simulation
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T10:19:16.298801+00:00
-- url     : https://prove2.me/theorems/a725c316-d1f4-4f85-9c74-972f01ebac87
-- title:
--   Simulation theorem for odd-cell sandboxed RAM subprogram calls
-- statement:
--   Let $q$ be a RAM subprogram, and let a host program $p$ contain its odd-cell sandboxed translation at offset $\mathrm{base}$ (`SandboxedOddAt p q base T ONE exit`), with even cells $T\ne\mathrm{ONE}$.
--
--   Suppose $q$, run from a state $s$, is at a `halt` instruction after $t$ operations. Let $s'$ be a host state whose odd cells $2a+1$ mirror the cells $a$ of $s$, whose cell `ONE` holds $1$, and whose program counter is $\mathrm{base}+3\,\mathrm{pc}(s)$. Then there is $\tau\le 3t+1$ such that the host state $s''=\mathrm{run}_p(s',\tau)$ satisfies:
--
--   1. $\mathrm{pc}(s'')=\mathrm{exit}$;
--   2. the odd cells of $s''$ mirror the final state $\mathrm{run}_q(s,t)$ of the subprogram;
--   3. every even host cell is unchanged, except the scratch cell $T$ among the natural cells.
--
--   This is the subroutine-call theorem with an unbounded host workspace: an arbitrary RAM program runs inside a host program with slowdown at most $3t+1$, while the host keeps arbitrarily much data in its even cells.
--
--   **Formalization Note.** The memory correspondence is `SandboxOddRel ONE` from `Def_WilliamsonShmoys_RAMSandboxOdd`.
-- source:
--   Subroutine-call infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSandboxOdd

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.sandbox_odd_simulation (p q : List PlanarRAMInstruction) (base T ONE exit : ℕ)
    (hTe : T % 2 = 0) (hOe : ONE % 2 = 0) (hTO : T ≠ ONE)
    (hp : SandboxedOddAt p q base T ONE exit) :
    ∀ (t : ℕ) (s s' : PlanarRAMState),
      q[(planarRAMRun q s t).pc]? = some PlanarRAMInstruction.halt →
      SandboxOddRel ONE s s' → s'.pc = base + 3 * s.pc →
      ∃ τ, τ ≤ 3 * t + 1 ∧
        (planarRAMRun p s' τ).pc = exit ∧
        SandboxOddRel ONE (planarRAMRun q s t) (planarRAMRun p s' τ) ∧
        (∀ a, a % 2 = 0 → a ≠ T → (planarRAMRun p s' τ).natMem a = s'.natMem a) ∧
        (∀ a, a % 2 = 0 → (planarRAMRun p s' τ).realMem a = s'.realMem a) := by sorry
