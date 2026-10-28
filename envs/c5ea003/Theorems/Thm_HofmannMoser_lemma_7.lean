-- Prove2me | Theorems.Thm_HofmannMoser_lemma_7
-- name    : HofmannMoser.lemma_7
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-28T00:51:49.751137+00:00
-- url     : https://prove2.me/theorems/51154005-1adc-4801-b724-2f1bc163283b
-- title:
--   Lemma 7: Closure of resource functions under addition and multiplication
-- statement:
--   This is Lemma 7 of Hofmann and Moser (TLCA 2015, p. 247), establishing that the class $\mathsf{RF}$ of unary resource functions is closed under pointwise addition and pointwise multiplication.
--
--   Let $S$ be a finite nonempty constructor signature (`FiniteConstructors C`), and let $r, r' : \text{Value } C \to \mathbb{Q}$ be unary resource functions (`IsResourceFunction C r` and `IsResourceFunction C r'`, meaning each is the potential of a length-$1$ resource annotation). Then both their pointwise sum and their pointwise product are resource functions:
--
--   $$(v \mapsto r(v) + r'(v)) \in \mathsf{RF} \quad\text{and}\quad (v \mapsto r(v) \cdot r'(v)) \in \mathsf{RF}.$$
--
--   Multiplicative closure relies on the Cartesian-product automaton construction (`TreeAutomaton.product` / `BasicFunction.product`), which multiplies accepting-run counts on every ground constructor value.
-- source:
--   Hofmann--Moser 2015, Multivariate Amortised Resource Analysis for Term Rewrite Systems, TLCA 2015, https://doi.org/10.4230/LIPIcs.TLCA.2015.241, Section 3, p. 247, Lemma 7

import Definitions.Def_HofmannMoser_Potential

universe u

namespace HofmannMoser

theorem lemma_7 {C : Nat → Type u} (S : FiniteConstructors C)
    {r r' : Value C → Rat} (hr : IsResourceFunction C r) (hr' : IsResourceFunction C r') :
    IsResourceFunction C (fun v ↦ r v + r' v) ∧
    IsResourceFunction C (fun v ↦ r v * r' v) := by sorry

end HofmannMoser
