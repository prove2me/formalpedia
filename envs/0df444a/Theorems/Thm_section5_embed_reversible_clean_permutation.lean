-- Prove2me | Theorems.Thm_section5_embed_reversible_clean_permutation
-- name    : section5_embed_reversible_clean_permutation
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:36:48.172384+00:00
-- url     : https://prove2.me/theorems/7c0087f2-bde8-4943-a3bd-c5cce2954840
-- title:
--   Embedding a clean reversible basis transformation
-- statement:
--   Let $L$ be a layered circuit on $d+a$ wires that is realizable over NOT/CNOT/Toffoli gates with at most $|L|$ gates and implements a basis transformation $f:\{0,1\}^d\to\{0,1\}^d$ with $a$ clean ancillas. Embed its data and ancilla wires disjointly into an $m$-wire register by $e$ and $h$. Then a NOT/CNOT/Toffoli circuit $C$ exists with
--
--   $$|C|\le|L|,\qquad U_C|z\rangle=|z[e\leftarrow f(z\circ e)]\rangle\quad\text{whenever }z\circ h=0^a.$$
--
--   Here the bracket updates only the embedded data wires. This transports a clean arithmetic implementation into an arbitrary surrounding register.
-- source:
--   Original embedding adapter in Solutions/Section5EmbeddedClassicalArithmetic.lean, lines 10–24, supporting Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. The reused clean-arithmetic embedding foundation is credited to Robin Kothari, accepted submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean.

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
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_embed_reversible_clean_permutation {main anc m : ℕ}
    (lc : LayeredCircuit (main+anc)) (f : Qubits main → Qubits main)
    (hrev : section5_RevRealizable lc) (hlc : lc.ImplementsOnClean (permMat f))
    (eMain : Fin main ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hdisj : ∀ i j, eMain i ≠ eAnc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ lc.size ∧
      ∀ z : Qubits m, (∀ j, z (eAnc j)=false) →
        act c.unitary (ket z)=ket (updateOn eMain z (f (z ∘ eMain))) := by sorry
