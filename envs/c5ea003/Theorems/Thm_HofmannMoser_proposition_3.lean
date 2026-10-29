-- Prove2me | Theorems.Thm_HofmannMoser_proposition_3
-- name    : HofmannMoser.proposition_3
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-28T00:51:19.29859+00:00
-- url     : https://prove2.me/theorems/d76c29b4-2a2b-4d33-af95-045e35e1d76a
-- title:
--   Proposition 3: Recursive decomposition of basic functions
-- statement:
--   This is Proposition 3 of Hofmann and Moser (TLCA 2015, p. 245), giving the bottom-up recursive decomposition of the basic resource function associated with a tree automaton.
--
--   Let $\mathcal{C}$ be an arity-indexed constructor signature (`C : Nat → Type u`), let $A$ be a bottom-up nondeterministic tree automaton over $\mathcal{C}$ (`TreeAutomaton C`), let $c \in \mathcal{C}_n$ be an $n$-ary constructor applied to ground constructor values $v_1, \dots, v_n$ (`vs : Fin n → Value C`), and let $\alpha \in \operatorname{Fin}(A.\text{stateCount})$ be a state of $A$. Write $(A, q)$ for the automaton $A$ rerooted at final state $q$ (`A.reroot q`) and $p_{(A, q)}$ for its basic resource function `(A.reroot q).basic`. Then
--
--   $$p_{(A, \alpha)}(c(v_1, \dots, v_n)) = \sum_{((\alpha_1, \dots, \alpha_n), \alpha) \in \Delta_A(c)} \prod_{i=1}^n p_{(A, \alpha_i)}(v_i).$$
--
--   This identity underpins the constructor typing rule and the potential-preservation theorem for the additive constructor shift $\triangleleft_c$ (Lemma 12).
--
--   **Formalization Note** The sum ranges over the filtered transition list `(A.rules n c).filter (fun tr ↦ tr.2 == α)` and the product over `Fin n` is computed via `(List.ofFn ...).foldl (· * ·) 1`, so the empty product for a nullary constructor ($n = 0$) evaluates to $1$.
-- source:
--   Hofmann--Moser 2015, Multivariate Amortised Resource Analysis for Term Rewrite Systems, TLCA 2015, https://doi.org/10.4230/LIPIcs.TLCA.2015.241, Section 3, p. 245, Proposition 3

import Definitions.Def_HofmannMoser_Potential

universe u

namespace HofmannMoser

theorem proposition_3 {C : Nat → Type u} (A : TreeAutomaton C) {n : Nat}
    (c : C n) (vs : Fin n → Value C) (α : Fin A.stateCount) :
    (A.reroot α).basic (.node c vs) =
      (((A.rules n c).filter (fun tr ↦ tr.2 == α)).map fun tr ↦
        (List.ofFn fun i ↦ (A.reroot (tr.1 i)).basic (vs i)).foldl (· * ·) 1).sum := by sorry

end HofmannMoser
