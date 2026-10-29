-- Prove2me | Theorems.Thm_HofmannMoser_lemma_9
-- name    : HofmannMoser.lemma_9
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-28T00:51:57.309282+00:00
-- url     : https://prove2.me/theorems/d43fa31e-026c-410b-9e82-0decfb661498
-- title:
--   Lemma 9: Diagonalization of binary multivariate basic functions
-- statement:
--   This is Lemma 9 of Hofmann and Moser (TLCA 2015, p. 248), showing that evaluating a binary multivariate basic function on a duplicated argument $(v, v)$ yields a unary basic function.
--
--   Let $S$ be a finite nonempty constructor signature (`FiniteConstructors C`), and let $p = (p_0, p_1) \in \mathsf{BF}(2)$ (`p : Fin 2 → BasicFunction C`) be a pair of basic resource functions with multivariate evaluation $p(v, v) = p_0(v) \cdot p_1(v)$ (`multivariateBasic p (fun _ ↦ v)`). Then there exists a unary basic resource function $p' \in \mathsf{BF}$ (`p' : BasicFunction C`) such that for every ground constructor value $v$ (`Value C`),
--
--   $$p(v, v) = p'(v).$$
--
--   This lemma justifies contracting shared variables in resource annotations via the sharing operator $\Upsilon$ (Lemma 13) and the typing rule `Typing.share`.
-- source:
--   Hofmann--Moser 2015, Multivariate Amortised Resource Analysis for Term Rewrite Systems, TLCA 2015, https://doi.org/10.4230/LIPIcs.TLCA.2015.241, Section 3, p. 248, Lemma 9

import Definitions.Def_HofmannMoser_Potential

universe u

namespace HofmannMoser

theorem lemma_9 {C : Nat → Type u} (S : FiniteConstructors C)
    (p : Fin 2 → BasicFunction C) :
    ∃ p' : BasicFunction C, ∀ v : Value C,
      multivariateBasic p (fun _ ↦ v) = p'.val v := by sorry

end HofmannMoser
