-- Prove2me | Theorems.Thm_section5_single_qex_vote_circuit
-- name    : section5_single_qex_vote_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:33:19.599497+00:00
-- url     : https://prove2.me/theorems/8e4ace53-417b-4ee6-8dd2-e90ee210fecc
-- title:
--   Circuit for one bounded-window QEX orientation vote
-- statement:
--   Let n≥1, 2^q≥2^40n² and fixed-point coefficient width a+1 with fractional precision f. Given example, label, accumulator, workspace and temporary wires satisfying the source's separation hypotheses, all scratch wires zero, a reversible circuit preserves every wire outside its accumulator and returns the final accumulator bit $$v=[\operatorname{ltf}_{u,0}(WZ)=-1]\mathbin{\mathrm{xor}}l,\qquad|C|\le128(n+a+34)^4+1.$$ If l is the true negative-label bit of w on Z, v is exactly the quantized orientation vote for w,u.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5SingleVoteCircuit.lean, lines 16–36. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_embed_classical_gate_action
import Theorems.Thm_section5_replace_wires_eq_update
import Theorems.Thm_section5_uniform_window_comparator
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm410Router

theorem section5_single_qex_vote_circuit {m n q a : ℕ}
    (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) (f : ℕ)
    (ov : Fin n → Fin (a+1) ↪ Fin m) (ex : Fin (n*q) ↪ Fin m)
    (p : Fin (n+a+(2*section5_window_precision n+1)+1) ↪ Fin m)
    (anc : Fin (n+a+(2*section5_window_precision n+1)+1+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t label : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, ov i j ≠ t) (hxt : ∀ j, ex j ≠ t)
    (hup : ∀ i j, ov i j ∉ Set.range p) (hxp : ∀ j, ex j ∉ Set.range p)
    (hxa : ∀ j k, ex j ≠ anc k) (hlp : label ∉ Set.range p) :
    ∃ c : Circuit gatesRev m, c.size ≤ 128*(n+a+34)^4+1 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ e, z (p e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          z' (p (Fin.last (n+a+(2*section5_window_precision n+1))))=
            xor (decide (ltf (WithLp.toLp 2 fun i => readFp (ov i) f z) 0
              (section5_bounded_window_vector q (gridPoint (z ∘ ex)))= -1)) (z label) ∧
          ∀ w : EuclideanSpace ℝ (Fin n),
            z label=decide (ltf w 0 (gridPoint (z ∘ ex))= -1) →
              z' (p (Fin.last (n+a+(2*section5_window_precision n+1))))=
                section5_quantized_vote w (WithLp.toLp 2 fun i => readFp (ov i) f z) (z ∘ ex) := by sorry
