-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_black_box_v2
-- name    : X25519Dalek.fnOk_black_box_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T19:14:06.446733+00:00
-- url     : https://prove2.me/theorems/66d8ff71-3188-464e-91c7-82a232cacad9
-- title:
--   subtle::black_box::<u8> — the compiled optimization barrier returns its argument
-- statement:
--   Total correctness of `subtle::black_box::<u8>` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`blackBoxU8Spec`): the low 8 bits of `w0` are $v$, and the caller owns the 16 bytes below the stack pointer. The postcondition: the low 8 bits of `w0` are $v$, and the stack frame is handed back.
--
--   subtle 2.6.1, src/lib.rs, lines 212–213: “This function is a best-effort attempt to prevent the compiler from knowing anything about the value of the returned `u8`, other than its type.”
--
--   **Replaces** `X25519Dalek.fnOk_black_box`. The Lean statement is the same, with the same hypotheses and conclusion, and it elaborates to the identical term. Only the preamble changed: it imports the definitions it uses instead of all of Mathlib, which cost every proof importing the old statement about 6.4 GB of the verifier's 7150 MiB.
-- source:
--   subtle 2.6.1 (https://crates.io/crates/subtle/2.6.1), src/lib.rs, lines 212–224 (black_box)

import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_black_box_v2 :
    fnOk
      "subtle::black_box::<u8>"
      (fun _ => blackBoxU8Spec) := by
  sorry

end X25519Dalek
