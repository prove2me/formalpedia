-- Prove2me | Theorems.Thm_section5_complex_matrix_product_circuit
-- name    : section5_complex_matrix_product_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:19:07.045505+00:00
-- url     : https://prove2.me/theorems/dac929c5-b244-5687-b9b1-4a2da982d987
-- title:
--   Reversible modular multiplication of complex integer matrices
-- statement:
--   Let $m,r,n,a,b,w$ be natural numbers. A map from $r$ input positions to $m$ circuit wires supplies bits encoding two complex $n\times n$ matrices $A$ and $B$: each real or imaginary entry of $A$ is an integer weighted sum of $a$ selected bits with coefficients $c_0,\ldots,c_{a-1}\in\mathbb Z$, and each entry of $B$ uses $b$ selected bits with coefficients $d_0,\ldots,d_{b-1}\in\mathbb Z$. Reserve $2n^2$ pairwise disjoint output registers of $w$ bits, an injectively placed workspace of $w+1$ bits, and a scratch wire $t$. Assume the outputs avoid all input and workspace wires; $t$ avoids all outputs, workspace wires, and input wires. There exists a circuit over the reversible gate set, of size at most
--
--   $$
--   (16w+6)(2nab)(2n^2),
--   $$
--
--   with the following action on every computational basis state whose outputs, workspace, and scratch wire are initially zero. It produces a computational basis state, preserves every wire outside the output registers, and writes each real or imaginary entry of $AB$ to its corresponding output register modulo $2^w$:
--
--   $$
--   \operatorname{value}(O_{\sigma,i,j})\equiv (AB)^{\sigma}_{ij}\pmod{2^w},\qquad \sigma\in\{\mathrm{Re},\mathrm{Im}\}.
--   $$
--
--   Here output bits are interpreted in least-significant-bit-first order, and the correspondence between the $2n^2$ registers and the component indices is the fixed indexing bijection of the construction. This supplies modular complex matrix multiplication with restored shared workspace; it makes no no-overflow assertion.
-- source:
--   Original auxiliary circuit construction supporting Section 5 of https://arxiv.org/html/2609.40331v3. Exact source: Solutions/Section5ComplexMatrixCircuit.lean, section5_complex_matrix_product_circuit, lines 72–99. Weighted input decoding, component indexing, and real/imaginary product components are defined in the same file, lines 12–24. This is a formalization-specific modular arithmetic component, not the paper's complete matrix-power or learning theorem.

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
import Definitions.Def_Section5Verified_Section5ComplexMatrixCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Mathlib
import Theorems.Thm_section5_batched_bilinear_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_complex_matrix_product_circuit {m r n a b w : ℕ}
    (data : Fin r → Fin m) (c : Fin a → ℤ) (d : Fin b → ℤ)
    (Are Aim : Fin n → Fin n → Fin a → Fin r)
    (Bre Bim : Fin n → Fin n → Fin b → Fin r)
    (p : Fin (2*n*n) → Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hdata : ∀ i j e, data j ≠ p i e) (hpa : ∀ i e j, p i e ≠ anc j)
    (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j) (hdt : ∀ j, data j ≠ t) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ ((16*w+6)*((n+n)*a*b))*(2*n*n) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, (bitsToNatLSB (z' ∘ p i):ZMod (2^w))=
            (section5_complex_product_component
              (section5_read_integer_matrix c Are Aim (z ∘ data))
              (section5_read_integer_matrix d Bre Bim (z ∘ data))
              (section5_complex_entry_index n i):ZMod (2^w)) := by sorry
