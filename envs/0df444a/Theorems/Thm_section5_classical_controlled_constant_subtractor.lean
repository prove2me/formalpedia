-- Prove2me | Theorems.Thm_section5_classical_controlled_constant_subtractor
-- name    : section5_classical_controlled_constant_subtractor
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:52:49.47239+00:00
-- url     : https://prove2.me/theorems/62f4bac9-d1a8-5209-a0d0-57213656062c
-- title:
--   Clean controlled constant subtraction with at most $16w$ gates
-- statement:
--   Let $w,a\in\mathbb N$. There exists a NOT/CNOT/Toffoli circuit $C$ on $(1+w)+(w+1)$ wires with $|C|\le16w$. For every control bit $b$ and least-significant-bit-first $w$-bit unsigned value $B$,
--
--   $$U_C|b,B,0^{w+1}\rangle=|b,(B-ba)\bmod2^w,0^{w+1}\rangle.$$
--
--   Subtraction is interpreted modulo $2^w$. The circuit preserves the control and restores all $w+1$ workspace bits.
-- source:
--   Original gatesRev realization in Solutions/Section5ReversibleAdder.lean, lines 86–95, supporting Section 5 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. Reused accepted arithmetic foundation: Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), credited in Solutions/Section5LcgArithmeticFoundation.lean.

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
import Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_Aux_w54_arith_ctrlAddConstInPlaceCircuit_implements
import Theorems.Thm_Aux_w54_arith_ctrlAddConstInPlaceFn_ctrlSubConstInPlaceFn
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_classical_controlled_constant_subtractor (w a : ℕ) :
    ∃ c : Circuit gatesRev ((1+w)+(w+1)), c.size ≤ 16*w ∧
      ∀ x : Qubits (1+w),
        act c.unitary (ket (padZero (1+w) (w+1) x))=
          ket (padZero (1+w) (w+1) (Aux_w54_arith.ctrlSubConstInPlaceFn w a x)) := by sorry
