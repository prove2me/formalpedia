-- Prove2me | Theorems.Thm_section5_signed_dot_no_overflow
-- name    : section5_signed_dot_no_overflow
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:54.288933+00:00
-- url     : https://prove2.me/theorems/8b3596e4-b637-4831-814c-169eac9fc1e9
-- title:
--   A signed dot product fits the chosen accumulator range
-- statement:
--   Let n,a,b be natural. Let u_i be signed two's-complement words of width a+1 and x_i signed words of width b+1, for i∈{1,…,n}. Their decoded integer dot product satisfies the strict bound $$\left|\sum_{i=1}^n\operatorname{signed}(u_i)\operatorname{signed}(x_i)\right|<2^{n+a+b}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5SignedComparator.lean, lines 23–26.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedWindow
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_twos_complement_residue
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_signed_dot_no_overflow {n a b : ℕ}
    (u : Fin n → Qubits (a+1)) (x : Fin n → Qubits (b+1)) :
    |∑ i : Fin n, section5_integer_bit_value (section5_twos_coefficient (a+1)) (u i)*
      section5_integer_bit_value (section5_twos_coefficient (b+1)) (x i)| < (2:ℤ)^(n+a+b) := by sorry
