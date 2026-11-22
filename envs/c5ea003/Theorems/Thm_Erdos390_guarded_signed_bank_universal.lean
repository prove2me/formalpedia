-- Prove2me | Theorems.Thm_Erdos390_guarded_signed_bank_universal
-- name    : Erdos390.guarded_signed_bank_universal
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-16T14:44:03.322159+00:00
-- url     : https://prove2.me/theorems/97225835-aa85-47bc-b4db-876d5545810d
-- title:
--   A guarded signed-unit reserve realizes every bounded integer correction
-- statement:
--   Let $P$ be a finite set of natural-number coordinates and let $\beta_p\in\mathbb N$. For each $p\in P$, reserve $\beta_p$ positive and $\beta_p$ negative slots. Each slot has two finite states of positive integer factors; replacing state zero by state one changes its prime-valuation vector by $+e_p$ or $-e_p$, according to the slot's sign.
--
--   Assume every state lies in a fixed legal set, avoids a fixed forbidden set, and is disjoint from every state of every other slot. For any integer vector $z$ with $|z_p|\le\beta_p$, there are prefix counts $u_p,v_p$ with $u_p+v_p\le\beta_p$ such that the corresponding chosen-state union $B$ is legal, avoids the forbidden set, and satisfies
--   $$v_q\!\left(\prod B\right)=v_q\!\left(\prod B_0\right)+\begin{cases}z_q&q\in P,\\0&q\notin P.\end{cases}$$
--   Here $B_0$ is the union of all zero states; unused slots retain that state. This proves the finite universality of a reserved bank once its literal factor states and joint guards have been constructed.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 5, Lemma precharged-universal-bank (finite signed-unit universality), and Section 10, bank-state-replacement and bank-final-valuation-change. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex . Complete finite Lean arguments: BankPathAlgebra.lean (twoSidedUnitPaths_boxUniversal), GuardedBankSelection.lean (exists_bounded_embeddedBankStateChoice), GuardedExactificationAlgebra.lean (chosenBankFactors_factorization_sub_base).

import Definitions.Def_erdos390_signed_bank
open scoped BigOperators
open Erdos390.WholePaper

theorem Erdos390.guarded_signed_bank_universal
    (P : Finset ℕ) (β : ↑P → ℕ)
    (state : SignedBankSlot β → Bool → Finset ℕ)
    (ambient forbidden : Finset ℕ)
    (hpositive : ∀ g b a, a ∈ state g b → 0 < a)
    (hlegal : ∀ g b, state g b ⊆ ambient)
    (hguard : ∀ g b, Disjoint forbidden (state g b))
    (hcross : ∀ g h, g ≠ h → ∀ b c, Disjoint (state g b) (state h c))
    (hchange : ∀ g,
      integerValuationVector ((state g true).prod id) -
          integerValuationVector ((state g false).prod id) =
        embeddedSignedBankSlotChange (fun p : ↑P ↦ p.1) g)
    (z : BankVector ↑P) (hz : ∀ p, |z p| ≤ (β p : ℤ)) :
    ∃ positive negative : ↑P → ℕ,
      (∀ p, positive p + negative p ≤ β p) ∧
      chosenBankFactors state (signedBankStateChoice positive negative) ⊆ ambient ∧
      Disjoint forbidden (chosenBankFactors state (signedBankStateChoice positive negative)) ∧
      ∀ q : ℕ,
        integerValuationVector
            ((chosenBankFactors state (signedBankStateChoice positive negative)).prod id) q =
          integerValuationVector ((baseBankFactors state).prod id) q +
            embeddedBankVector (fun p : ↑P ↦ p.1) z q := by sorry
