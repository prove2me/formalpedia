-- Prove2me | Theorems.Thm_section5_compaction_gate_bound
-- name    : section5_compaction_gate_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:05.774631+00:00
-- url     : https://prove2.me/theorems/b9d98715-b055-518f-9e70-e7d81eeaaa46
-- title:
--   Explicit logarithmic compaction gate bound
-- statement:
--   Let $n,K\in\mathbb N$ with $n\ge1$, and let $\lceil\log_2 n\rceil$ denote the least integer $r$ with $n\le2^r$. Then
--
--   $$2K\big(\lceil\log_2 n\rceil+1\big)\le\frac6{\log2}\,K\log(n+1).$$
--
--   This gives an explicit constant in the $O(K\log(n+1))$ gate bound for compaction when each particle register has $\lceil\log_2 n\rceil+1$ wires.
-- source:
--   Original gate-count auxiliary result for Theorem 5.4, Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Formalization: Solutions/Section5Routing.lean, lines 269–276.

import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_gates12
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_compaction_gate_bound (n K : ℕ) (hn : 1 ≤ n) :
    ((2*K*(Nat.clog 2 n+1) : ℕ) : ℝ) ≤ (6/Real.log 2)*K*Real.log (n+1) := by sorry
