-- Prove2me | Theorems.Thm_section5_affine_copy_prefix_action
-- name    : section5_affine_copy_prefix_action
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:06.388733+00:00
-- url     : https://prove2.me/theorems/b66141ce-6e04-5014-813b-0aecfc3b64e5
-- title:
--   Exact action of an affine-copy circuit prefix
-- statement:
--   Let m,w be natural numbers, let src select w source wires, let dst inject w destination wires into the m-wire register, and assume every source wire is outside dst. Let ν_i be fixed Boolean complements and 0≤k≤w. For every basis string z, the source-defined k-stage affine-copy circuit maps |z⟩ to |z'⟩, preserves all wires outside dst, and satisfies
--
--   $$z'_{\mathrm{dst}(i)}=\begin{cases}z_{\mathrm{dst}(i)}\mathbin{\mathrm{xor}}(z_{\mathrm{src}(i)}\mathbin{\mathrm{xor}}
--   u_i)&i<k,\\z_{\mathrm{dst}(i)}&i\ge k.\end{cases}$$
--
--   The destination need not start at zero, and source wires may repeat.
-- source:
--   Original auxiliary circuit identity supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5AffineCopy.lean, lines 41–45; circuit and state definitions, lines 10–25.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5AffineCopy
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_boolean_gate_action
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm410Router

theorem section5_affine_copy_prefix_action {m w : ℕ} (src : Fin w → Fin m)
    (dst : Fin w ↪ Fin m) (neg : Fin w → Bool) (hdisj : ∀ i j, src i ≠ dst j)
    (k : ℕ) (hk : k ≤ w) (z : Qubits m) :
    act (section5_affine_copy_prefix src dst neg hdisj k hk).unitary (ket z)=
      ket (section5_affine_prefix_state src dst neg k z) := by sorry
