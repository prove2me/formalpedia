-- Prove2me | Theorems.Thm_X25519Dalek_fnOk_differential_add_and_double
-- name    : X25519Dalek.fnOk_differential_add_and_double
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-22T22:19:54.850207+00:00
-- url     : https://prove2.me/theorems/9f9e5f42-d4ff-40f8-a9dc-38c6b1958a59
-- title:
--   montgomery::differential_add_and_double — the compiled ladder step
-- statement:
--   Total correctness of `curve25519_dalek::montgomery::differential_add_and_double` in the AArch64 object code (`x25519CliMultiLib`; `fnOk`). For every placement of the library that the linker could produce (`Placeable`), every frame $R$ and every entry state at the function's address with the code of all 19 blocks loaded and the stack pointer 16-byte aligned, whose memory satisfies the precondition separately from $R$, execution terminates, returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding, and never panics, exits or runs out of memory.
--
--   The precondition (`montDiffAddAndDoubleSpec`): `x0` and `x1` hold the addresses of two 80-byte projective points $P = (U_P : W_P)$ and $Q = (U_Q : W_Q)$ with every limb below $2^{53}$, and `x2` the address of a 40-byte `FieldElement51` $u_1$ with every limb below $2^{54}$. The caller owns the three buffers, the read-only constant $121666$ at its placed address, and the 1,056 bytes below the stack pointer. The postcondition: the two buffers hold new points, every limb below $2^{52}$, whose values mod $p$ are the two components of `montDiffAddAndDouble` $u_1$ $P$ $Q$: $P \gets (AA \cdot BB : E(AA + 121665\,E))$ and $Q \gets ((DA + CB)^2 : u_1 (DA - CB)^2)$ in RFC 7748's notation, with $u_1, P, Q$ taken mod $p$; $u_1$, the constant and the stack frame are handed back.
--
--   curve25519-dalek 5.0.0, src/montgomery.rs, lines 415–428: “Perform the double-and-add step of the Montgomery ladder. Given projective points $(U_P : W_P) = u(P)$, $(U_Q : W_Q) = u(Q)$, and the affine difference $u_{P-Q} = u(P-Q)$, set $(U_P : W_P) \gets u([2]P)$ and $(U_Q : W_Q) \gets u(P + Q)$.”
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), src/montgomery.rs, lines 415–428 (differential_add_and_double)

import Mathlib
import Definitions.Def_X25519Dalek_Spec

namespace X25519Dalek

theorem fnOk_differential_add_and_double :
    fnOk
      "curve25519_dalek::montgomery::differential_add_and_double"
      montDiffAddAndDoubleSpec := by
  sorry

end X25519Dalek
