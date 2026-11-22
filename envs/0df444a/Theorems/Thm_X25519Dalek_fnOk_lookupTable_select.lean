-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_lookupTable_select
-- name    : X25519Dalek.fnOk_lookupTable_select
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T21:42:24.253806+00:00
-- url     : https://prove2.me/theorems/073504d5-b800-492f-a56e-ba7bac3bd9a1
-- title:
--   LookupTable<AffineNielsPoint>::select — the compiled signed table lookup
-- statement:
--   Total correctness of `<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`lookupTableAffineNielsSelectSpec`): `x0` holds the address `out` of a 120-byte result buffer, `x1` the address of a read-only table of 960 bytes (8 entries of 120 bytes, every limb below $2^{53}$), and the low 8 bits of `x2` are $x$. The caller owns the result buffer and the 192 bytes below the stack pointer. The postcondition: `out` holds 120 bytes with every limb below $2^{53}$ whose three field values mod $p$ are `edSelectAffineNiels table x`: for $x = \pm j$ with $1 \le j \le 8$ the entry $j - 1$, for any other byte the identity $(1, 1, 0)$; and if $x$ is negative as a signed byte, the first two values swapped and the third negated mod $p$. The table and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/window.rs, line 53: “Given $-8 \leq x \leq 8$, return $xP$ in constant time.”
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/window.rs, lines 53–54 (LookupTable::select)

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_lookupTable_select :
    fnOk
      "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select"
      (fun _ => lookupTableAffineNielsSelectSpec) := by
  sorry

end X25519Dalek
