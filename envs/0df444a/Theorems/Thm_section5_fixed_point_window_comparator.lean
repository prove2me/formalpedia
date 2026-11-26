-- Prove2me | Theorems.Thm_section5_fixed_point_window_comparator
-- name    : section5_fixed_point_window_comparator
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:22:42.747801+00:00
-- url     : https://prove2.me/theorems/bba2a051-c1dc-5897-84ca-78e8cef6dc72
-- title:
--   Fixed-point window-label comparator circuit
-- statement:
--   Let s+b+1≤q−1 and W=n+a+b+1. Given n (a+1)-bit fixed-point coefficient registers of precision f and n q-bit example coordinates, embed a zero W-bit accumulator, zero (W+1)-bit workspace and temporary bit with the source's disjointness conditions; examples avoid the workspace. A reversible circuit preserves every wire outside the accumulator and returns its top bit r satisfying $$r=0\iff\operatorname{ltf}_{u,0}(\text{centered middle window of the example})=1,\quad |C|\le(16W+6)n(a+2)(b+1).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5WindowComparator.lean, lines 15–31. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5RealWindow
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Definitions.Def_Section5Verified_Section5WindowComparator
import Definitions.Def_Section5Verified_Section5WindowDotIdentity
import Mathlib
import Theorems.Thm_section5_offset_integer_comparator
import Theorems.Thm_section5_window_integer_dot_label
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm49Primitives

theorem section5_fixed_point_window_comparator {m n q a b : ℕ}
    (s f : ℕ) (hfit : s+(b+1) ≤ q-1)
    (ov : Fin n → (Fin (a+1) ↪ Fin m)) (ex : Fin (n*q) ↪ Fin m)
    (p : Fin (n+a+b+1) ↪ Fin m) (anc : Fin ((n+a+b+1)+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, ov i j ≠ t) (hxt : ∀ j, ex j ≠ t)
    (hup : ∀ i j, ov i j ∉ Set.range p) (hxp : ∀ j, ex j ∉ Set.range p)
    (hxa : ∀ j k, ex j ≠ anc k) :
    ∃ circ : Circuit gatesRev m, circ.size ≤
        (16*(n+a+b+1)+6)*(n*(a+2)*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i, z (p i)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (ltf (WithLp.toLp 2 (fun i => readFp (ov i) f z)) 0
            (section5_real_window_vec ((2:ℤ)^s) ((2:ℤ)^b) (gridSpacing (2^q))
              (gridPoint (z ∘ ex)))=1 ↔ z' (p (Fin.last (n+a+b)))=false) := by sorry
