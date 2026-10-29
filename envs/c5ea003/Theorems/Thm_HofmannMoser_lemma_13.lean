-- Prove2me | Theorems.Thm_HofmannMoser_lemma_13
-- name    : HofmannMoser.lemma_13
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-28T00:52:30.202031+00:00
-- url     : https://prove2.me/theorems/b21cd386-5bd7-4fb1-a982-830f5f645385
-- title:
--   Lemma 13: Potential preservation under the variable-sharing operator $\Upsilon$
-- statement:
--   This is Lemma 13 of Hofmann and Moser (TLCA 2015, p. 249), establishing that the variable-sharing operator $\Upsilon$ preserves potential when the last two coordinates of a value tuple are equal.
--
--   Let $S$ be a finite nonempty constructor signature (`FiniteConstructors C`), let $P$ be a representative policy (`RepPolicy C`), let $Q$ be a resource annotation of length $m + 2$ (`Annotation C (m + 2)`), let $w_1, \dots, w_m$ (`ws : Fin m → Value C`) be prefix values, and let $v$ (`Value C`) be a shared ground constructor value. Then
--
--   $$\Phi(w_1, \dots, w_m, v, v : Q) = \Phi(w_1, \dots, w_m, v : \Upsilon(Q)),$$
--
--   where $\Upsilon(Q)$ (`annotationShare S P Q`) replaces the last two basic functions of each entry in $Q$ by their Cartesian-product basic function (`BasicFunction.product S P`).
--
--   Lemma 13 establishes soundness of the structural sharing rule (`Typing.share`) in Figure 2.
-- source:
--   Hofmann--Moser 2015, Multivariate Amortised Resource Analysis for Term Rewrite Systems, TLCA 2015, https://doi.org/10.4230/LIPIcs.TLCA.2015.241, Section 3, p. 249, Lemma 13

import Definitions.Def_HofmannMoser_Potential

universe u

namespace HofmannMoser

theorem lemma_13 {C : Nat → Type u} {m : Nat} (S : FiniteConstructors C)
    (P : RepPolicy C) (Q : Annotation C (m + 2))
    (ws : Fin m → Value C) (v : Value C) :
    potential Q (Fin.addCases ws (fun _ ↦ v)) =
      potential (annotationShare S P Q) (Fin.addCases ws (fun _ ↦ v)) := by sorry

end HofmannMoser
