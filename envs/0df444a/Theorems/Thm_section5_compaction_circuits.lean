-- Prove2me | Theorems.Thm_section5_compaction_circuits
-- name    : section5_compaction_circuits
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:38.224228+00:00
-- url     : https://prove2.me/theorems/69552d85-259e-5c54-81a6-972e1eb5d63c
-- title:
--   Outcome-dependent compaction of nonblank particle registers
-- statement:
--   Embed $2K$ particle registers of $s$ qubits each into an $m$-qubit register. Let $t\in\{0,1\}^{2K}$ be a measured blank pattern, with $t_j=0$ denoting a nonblank register. There exists a family of one- and two-qubit circuits $W_t$, each of size at most $2Ks$, such that whenever at least $K$ entries of $t$ are zero, some permutation $\sigma$ of the particle registers satisfies
--
--   $$t_{\sigma(k)}=0\ (0\le k<K),\qquad U_{W_t}|x\rangle=|\operatorname{permPart}_{\sigma}(x)\rangle\quad\text{for every basis string }x.$$
--
--   The selected circuit routes $K$ nonblank registers to the first $K$ particle positions and fixes all wires outside the particle block.
-- source:
--   Original exact routing construction for the outcome-dependent compaction in Theorem 5.4, Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Formalization: Solutions/Section5Routing.lean, lines 225–249.

import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5Routing
import Mathlib
import Theorems.Thm_section5_embedded_wire_permutation
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_compaction_circuits {m K s : ℕ}
    (partEmb : Fin (2*K*s) ↪ Fin m) :
    ∃ W : Qubits (2*K) → Circuit gates12 m,
      (∀ t, (W t).size ≤ 2*K*s) ∧
      ∀ t : Qubits (2*K), K ≤ (Finset.univ.filter (fun j => t j=false)).card →
        ∃ σ : Equiv.Perm (Fin (2*K)),
          (∀ k : Fin K, t (σ ⟨k.val,by omega⟩)=false) ∧
          ∀ x : Qubits m, act (W t).unitary (ket x) = ket (permPartReg54 partEmb σ x) := by sorry
