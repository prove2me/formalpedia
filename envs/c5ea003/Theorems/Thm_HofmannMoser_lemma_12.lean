-- Prove2me | Theorems.Thm_HofmannMoser_lemma_12
-- name    : HofmannMoser.lemma_12
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-28T00:52:14.215099+00:00
-- url     : https://prove2.me/theorems/56b47aca-0c96-442c-9104-2a3960bf9711
-- title:
--   Lemma 12: Potential preservation under the additive constructor shift $\triangleleft_c$
-- statement:
--   This is Lemma 12 of Hofmann and Moser (TLCA 2015, p. 248), proving that the additive constructor shift $\triangleleft_c$ preserves potential exactly when a constructor term $c(v_1, \dots, v_n)$ is decomposed into its arguments $v_1, \dots, v_n$.
--
--   Let $P$ be a representative policy (`RepPolicy C`), let $c \in \mathcal{C}_n$ be an $n$-ary constructor, let $Q$ be a resource annotation of length $m + 1$ (`Annotation C (m + 1)`), and let $w_1, \dots, w_m$ (`ws : Fin m → Value C`) and $v_1, \dots, v_n$ (`vs : Fin n → Value C`) be ground constructor values. Then
--
--   $$\Phi(w_1, \dots, w_m, c(v_1, \dots, v_n) : Q) = \Phi(w_1, \dots, w_m, v_1, \dots, v_n : \triangleleft_c(Q)).$$
--
--   Lemma 12 is the fundamental algebraic identity behind both the constructor introduction rule (`Typing.constructor`) and the left-hand-side pattern expansion of rewrite rules (`PatternExpansion`, Definition 15).
--
--   **Formalization Note** The tuple $(w_1, \dots, w_m, c(v_1, \dots, v_n))$ of length $m + 1$ is represented by `Fin.addCases ws (fun _ ↦ Value.node c vs)`, and the tuple $(w_1, \dots, w_m, v_1, \dots, v_n)$ of length $m + n$ by `Fin.addCases ws vs`.
-- source:
--   Hofmann--Moser 2015, Multivariate Amortised Resource Analysis for Term Rewrite Systems, TLCA 2015, https://doi.org/10.4230/LIPIcs.TLCA.2015.241, Section 3, p. 248, Lemma 12

import Definitions.Def_HofmannMoser_Potential

universe u

namespace HofmannMoser

theorem lemma_12 {C : Nat → Type u} {m n : Nat} (P : RepPolicy C)
    (c : C n) (Q : Annotation C (m + 1))
    (ws : Fin m → Value C) (vs : Fin n → Value C) :
    potential Q (Fin.addCases ws (fun _ ↦ Value.node c vs)) =
      potential (additiveShift P c Q) (Fin.addCases ws vs) := by sorry

end HofmannMoser
