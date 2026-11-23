-- Prove2me | Theorems.Thm_X25519Dalek_steps_keepsFrozen_v2
-- name    : X25519Dalek.steps_keepsFrozen_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:20.312135+00:00
-- url     : https://prove2.me/theorems/b6cb1fba-dca8-49c0-ba3b-02fe7c1703a9
-- title:
--   Execution of the Arm64 model never changes a frozen (read-only or executable) byte
-- statement:
--   For every program $P$ and states $s, s'$ of the published Arm64 machine model (`Def_Arm64_ISA_Semantics`): if $s'$ is reachable from $s$ in zero or more steps of $P$ (`Arm64.Steps P s s'`), then the memory of $s'$ keeps the frozen part of the memory of $s$ (`Memory.KeepsFrozen`): at every address that is frozen in $s$ — mapped with a permission that is readable or executable and not writable — the byte, the permission, the lazily-freed flag and the anonymous flag are the same in $s'$ as in $s$. Nothing is claimed about addresses not frozen in $s$.
--
--   The statement holds for every program: an executed instruction stores only to bytes it has checked writable (writable and not executable), the supervisor-call handler is wrapped (`evalSvc`) so that it restores frozen cells, an extern hook steps only when it keeps frozen memory, and the halting and faulting steps leave memory unchanged. It is DeepMind's `Steps.keepsFrozen` (google-deepmind/code-verification @ 8c8d371f, ProofLib/Invariant.lean). In the x25519-dalek mission it shows that a block's code is still loaded after it returns from a call made through another block's `fnOk` contract, which the contract itself does not say.
--
--   **Replaces** `X25519Dalek.steps_keepsFrozen`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), arm64-semantics/ProofLib/Invariant.lean, theorem Steps.keepsFrozen, https://github.com/google-deepmind/code-verification

import Definitions.Def_Arm64_ISA_Semantics

namespace X25519Dalek

theorem steps_keepsFrozen_v2 {prog : Arm64.Program} {s s' : Arm64.State} (h : Arm64.Steps prog s s') :
    s.mem.KeepsFrozen s'.mem := by
  sorry

end X25519Dalek
