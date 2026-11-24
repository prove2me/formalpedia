-- Prove2me | Theorems.Thm_WilliamsonShmoys_sandbox_simulation
-- name    : WilliamsonShmoys.sandbox_simulation
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:15:58.8528+00:00
-- url     : https://prove2.me/theorems/8e806904-7ae8-47bc-affd-65bd73067326
-- title:
--   Simulation theorem for sandboxed RAM subprogram calls
-- statement:
--   Let $q$ be a RAM subprogram and let a host program $p$ contain its sandboxed translation at offset $\mathrm{base}$ (`SandboxedAt p q base o T O exit`), with scratch cell $T$ and offset cell $O$ satisfying $T,O<o$ and $T\ne O$.
--
--   Suppose $q$, run from a state $s$, sits at a `halt` instruction after $t$ operations. Let $s'$ be a host state whose cells $a+o$ mirror the cells $a$ of $s$, whose cell $O$ holds $o$, and whose program counter is $\mathrm{base}+2\,\mathrm{pc}(s)$. Then there is $\tau\le 2t+1$ such that the host state $s''=\mathrm{run}_p(s',\tau)$ satisfies:
--
--   1. $\mathrm{pc}(s'')=\mathrm{exit}$;
--   2. the cells $a+o$ of $s''$ mirror the final state $\mathrm{run}_q(s,t)$ of the subprogram;
--   3. every host cell $a<o$ is unchanged, except the scratch cell $T$ among the natural cells.
--
--   This is the subroutine-call theorem: an arbitrary RAM program can be run inside a host program, with at most a factor-$2$ (plus one) slowdown, without touching the host's working memory below $o$. In the mission it allows the Baker shifting program to call the exact tree-width solver $k$ times while keeping its own data.
--
--   **Formalization Note.** The memory correspondence is `SandboxRel o O`; cells not of the form $a+o$ with $a\ge0$ are exactly the cells below $o$.
-- source:
--   Subroutine-call infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSandbox

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.sandbox_simulation (p q : List PlanarRAMInstruction) (base o T O exit : ℕ)
    (hT : T < o) (hO : O < o) (hTO : T ≠ O)
    (hp : SandboxedAt p q base o T O exit) :
    ∀ (t : ℕ) (s s' : PlanarRAMState),
      q[(planarRAMRun q s t).pc]? = some PlanarRAMInstruction.halt →
      SandboxRel o O s s' → s'.pc = base + 2 * s.pc →
      ∃ τ, τ ≤ 2 * t + 1 ∧
        (planarRAMRun p s' τ).pc = exit ∧
        SandboxRel o O (planarRAMRun q s t) (planarRAMRun p s' τ) ∧
        (∀ a, a < o → a ≠ T → (planarRAMRun p s' τ).natMem a = s'.natMem a) ∧
        (∀ a, a < o → (planarRAMRun p s' τ).realMem a = s'.realMem a) := by sorry
