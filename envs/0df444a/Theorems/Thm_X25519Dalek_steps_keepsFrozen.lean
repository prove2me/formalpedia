-- Prove2me | Theorems.Thm_X25519Dalek_steps_keepsFrozen
-- name    : X25519Dalek.steps_keepsFrozen
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T12:09:31.473288+00:00
-- url     : https://prove2.me/theorems/071b8c16-e630-4bd7-bbc0-a81a117e8b23
-- title:
--   Execution of the Arm64 model never changes a frozen (read-only or executable) byte
-- statement:
--   For every program $P$ and states $s, s'$ of the published Arm64 machine model (`Def_Arm64_ISA_Semantics`): if $s'$ is reachable from $s$ in zero or more steps of $P$ (`Arm64.Steps P s s'`), then the memory of $s'$ keeps the frozen part of the memory of $s$ (`Memory.KeepsFrozen`): at every address that is frozen in $s$ — mapped with a permission that is readable or executable and not writable — the byte, the permission, the lazily-freed flag and the anonymous flag are the same in $s'$ as in $s$. Nothing is claimed about addresses not frozen in $s$.
--
--   The statement holds for every program: an executed instruction stores only to bytes it has checked writable (writable and not executable), the supervisor-call handler is wrapped (`evalSvc`) so that it restores frozen cells, an extern hook steps only when it keeps frozen memory, and the halting and faulting steps leave memory unchanged. It is DeepMind's `Steps.keepsFrozen` (google-deepmind/code-verification @ 8c8d371f, ProofLib/Invariant.lean). In the x25519-dalek mission it shows that a block's code is still loaded after it returns from a call made through another block's `fnOk` contract, which the contract itself does not say.
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), arm64-semantics/ProofLib/Invariant.lean, theorem Steps.keepsFrozen, https://github.com/google-deepmind/code-verification

import Mathlib
import Definitions.Def_Arm64_ISA_Semantics

namespace X25519Dalek

theorem steps_keepsFrozen {prog : Arm64.Program} {s s' : Arm64.State} (h : Arm64.Steps prog s s') :
    s.mem.KeepsFrozen s'.mem := by
  sorry

end X25519Dalek
