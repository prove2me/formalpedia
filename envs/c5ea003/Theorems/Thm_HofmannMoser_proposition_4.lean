-- Prove2me | Theorems.Thm_HofmannMoser_proposition_4
-- name    : HofmannMoser.proposition_4
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-28T00:51:36.964075+00:00
-- url     : https://prove2.me/theorems/247cc268-56b0-4ea4-804a-44b8c8461dbc
-- title:
--   Proposition 4: Exponential upper bound on basic functions ($p_A(v) \le q^{|v|}$)
-- statement:
--   This is Proposition 4 of Hofmann and Moser (TLCA 2015, p. 246), bounding the number of accepting runs of a tree automaton in terms of its state count and the size of the input value.
--
--   Let $A$ be a bottom-up nondeterministic tree automaton (`TreeAutomaton C`) with $q = A.\text{stateCount}$ states, and let $v$ be a ground constructor value (`Value C`) of size $|v| = v.\text{size}$ (the total number of constructor symbols occurring in $v$). Then the basic resource function $p_A(v) = A.\text{basic}\,v$ satisfies
--
--   $$p_A(v) \le q^{|v|}.$$
--
--   This bound shows that every basic resource function grows at most exponentially in the size of the input value, and provides the baseline growth estimate refined by polynomial tree automata in Section 5 of the paper.
--
--   **Formalization Note** In `TreeAutomaton C`, transition lists `A.rules n c` are duplicate-free (`no_duplicate_rules`), so for each target state $\alpha$ there are at most $q^n$ transitions $c(\alpha_1, \dots, \alpha_n) \to \alpha$.
-- source:
--   Hofmann--Moser 2015, Multivariate Amortised Resource Analysis for Term Rewrite Systems, TLCA 2015, https://doi.org/10.4230/LIPIcs.TLCA.2015.241, Section 3, p. 246, Proposition 4

import Definitions.Def_HofmannMoser_Potential

universe u

namespace HofmannMoser

theorem proposition_4 {C : Nat → Type u} (A : TreeAutomaton C) (v : Value C) :
    A.basic v ≤ A.stateCount ^ v.size := by sorry

end HofmannMoser
