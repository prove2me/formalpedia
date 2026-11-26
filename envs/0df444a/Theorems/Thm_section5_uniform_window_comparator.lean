-- Prove2me | Theorems.Thm_section5_uniform_window_comparator
-- name    : section5_uniform_window_comparator
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:25:37.455883+00:00
-- url     : https://prove2.me/theorems/8bd7dad2-6007-53ee-9878-3e7573e63898
-- title:
--   Uniform polynomial-size window-label comparator
-- statement:
--   Let n≥1 and 2^q≥2^40n². For n fixed-point coefficient registers of width a+1 and precision f, a grid example, and clean accumulator, workspace and temporary bit with the source's separation hypotheses, there exists a reversible circuit preserving every wire outside its accumulator whose top bit r obeys $$r=0\iff\operatorname{ltf}_{u,0}(\text{bounded-window example})=1,\qquad |C|\le128(n+a+34)^4.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5WindowComparator.lean, lines 68–84. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Definitions.Def_Section5Verified_Section5RealWindow
import Mathlib
import Theorems.Thm_section5_fixed_point_window_comparator
import Theorems.Thm_section5_large_grid_fits_window
import Theorems.Thm_section5_middle_window_scales
import Theorems.Thm_section5_window_precision_bounds
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm49Primitives

theorem section5_uniform_window_comparator {m n q a : ℕ}
    (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) (f : ℕ)
    (ov : Fin n → (Fin (a+1) ↪ Fin m)) (ex : Fin (n*q) ↪ Fin m)
    (p : Fin (n+a+(2*section5_window_precision n+1)+1) ↪ Fin m)
    (anc : Fin ((n+a+(2*section5_window_precision n+1)+1)+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, ov i j ≠ t) (hxt : ∀ j, ex j ≠ t)
    (hup : ∀ i j, ov i j ∉ Set.range p) (hxp : ∀ j, ex j ∉ Set.range p)
    (hxa : ∀ j k, ex j ≠ anc k) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ 128*(n+a+34)^4 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i, z (p i)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (ltf (WithLp.toLp 2 (fun i => readFp (ov i) f z)) 0
            (section5_bounded_window_vector q (gridPoint (z ∘ ex)))=1 ↔
              z' (p (Fin.last (n+a+(2*section5_window_precision n+1))))=false) := by sorry
