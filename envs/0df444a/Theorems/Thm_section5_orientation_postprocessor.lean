-- Prove2me | Theorems.Thm_section5_orientation_postprocessor
-- name    : section5_orientation_postprocessor
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:43:33.81884+00:00
-- url     : https://prove2.me/theorems/e4d4abae-3f46-4462-9750-9f9d9c9358be
-- title:
--   Reversible orientation postprocessor for three labelled examples
-- statement:
--   Let n≥1 and 2^q≥2^40n². Provide a fixed-point input vector of component width a+1 and precision f, three examples with label bits, zero vote accumulators, zero sign control, zero workspace and zero outputs of width a+2, satisfying all register-separation hypotheses in the source. There is a reversible circuit with $$|C|\le3(128(n+a+34)^4+1)+3+19(a+2)n.$$ Whenever labels are the true negative threshold bits for w, its decoded output equals the source's majority-oriented input direction. All wires outside vote accumulators, sign control and outputs are preserved.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5OrientationPostprocessor.lean, lines 18–50. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5OrientationPostprocessor
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Mathlib
import Theorems.Thm_section5_majority_sign_circuit
import Theorems.Thm_section5_three_vote_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

theorem section5_orientation_postprocessor {m n q a : ℕ}
    (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) (f : ℕ)
    (input : Fin n → Fin (a+1) ↪ Fin m) (output : Fin n → Fin (a+2) ↪ Fin m)
    (ex : Fin 3 → Fin (n*q) ↪ Fin m) (label : Fin 3 ↪ Fin m)
    (p : Fin 3 → Fin (n+a+(2*section5_window_precision n+1)+1) ↪ Fin m)
    (anc : Fin (n+a+(2*section5_window_precision n+1)+1+1) ↪ Fin m) (t : Fin m)
    (signAnc : Fin (a+3) ↪ Fin m) (ctrl : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e b, p i e ≠ p j b)
    (hpa : ∀ i e j, p i e ≠ anc j) (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i e, input i e ≠ t) (hxt : ∀ i e, ex i e ≠ t)
    (hup : ∀ i e j, input i e ∉ Set.range (p j))
    (hxp : ∀ i e j, ex i e ∉ Set.range (p j))
    (hxa : ∀ i e j, ex i e ≠ anc j) (hlp : ∀ i j, label i ∉ Set.range (p j))
    (hcp : ∀ j, ctrl ∉ Set.range (p j))
    (hsap : ∀ e j, signAnc e ∉ Set.range (p j))
    (hop : ∀ i e j, output i e ∉ Set.range (p j))
    (hopair : ∀ i j, i ≠ j → ∀ e b, output i e ≠ output j b)
    (hio : ∀ i j e b, input i e ≠ output j b)
    (hco : ∀ i e, ctrl ≠ output i e) (hcsa : ∀ e, ctrl ≠ signAnc e)
    (hosa : ∀ i e b, output i e ≠ signAnc b) (hic : ∀ i e, input i e ≠ ctrl) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ (128*(n+a+34)^4+1)*3+3+19*(a+2)*n ∧
      ∀ z : Qubits m, z t=false → (∀ e, z (anc e)=false) → (∀ i e, z (p i e)=false) →
        z ctrl=false → (∀ e, z (signAnc e)=false) → (∀ i e, z (output i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → j ≠ ctrl →
            (∀ i, j ∉ Set.range (output i)) → z' j=z j) ∧
          ∀ w : EuclideanSpace ℝ (Fin n),
            (∀ i, z (label i)=decide (ltf w 0 (gridPoint (z ∘ ex i))= -1)) →
              (WithLp.toLp 2 fun i => readFp (section5_msb_register (output i)) f z')=
                section5_oriented_direction w
                  (WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z)
                  (z ∘ ex 0,z ∘ ex 1,z ∘ ex 2) := by sorry
