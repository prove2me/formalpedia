-- Prove2me | Theorems.Thm_section5_reversible_probMixed
-- name    : section5_reversible_probMixed
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:02:54.132423+00:00
-- url     : https://prove2.me/theorems/d16519a2-df0b-4257-9185-ddd8f6d33749
-- title:
--   Mixed measurement law after reversible postprocessing
-- statement:
--   Let C be any reversible m-wire circuit, ρ any complex matrix on the bit basis, and P a decidable basis event. There exists a permutation F representing C on basis vectors, and its event measurement functional satisfies $$\operatorname{probMixed}(U_C,\rho,P)=\sum_x\mathbf1_{P(F(x))}\operatorname{Re}\rho_{xx}.$$ Positivity or normalization of ρ is not assumed for this algebraic identity.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ClassicalMeasurementLaw.lean, lines 29–33.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Mathlib
import Theorems.Thm_section5_basis_permutation_conjugation
import Theorems.Thm_section5_reversible_circuit_permutation
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_reversible_probMixed {m : ℕ} (c : Circuit gatesRev m)
    (ρ : Matrix (Qubits m) (Qubits m) ℂ) (P : Qubits m → Prop) [DecidablePred P] :
    ∃ f : Equiv.Perm (Qubits m),
      (∀ x, act c.unitary (ket x)=ket (f x)) ∧
      probMixed c.unitary ρ P=∑ x : Qubits m, if P (f x) then (ρ x x).re else 0 := by sorry
