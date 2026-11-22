-- Prove2me | Theorems.Thm_Erdos390_marked_path_signed_bank_spec
-- name    : Erdos390.marked_path_signed_bank_spec
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-16T15:12:05.982188+00:00
-- url     : https://prove2.me/theorems/3fa9de49-67d0-4dd1-a5cc-a125b9c26616
-- title:
--   Marked paths produce disjoint signed-unit bank states
-- statement:
--   Suppose the coordinates $P$ of a marked-path bank are all prime. Then every factor in every state is positive, states of different slots are disjoint for either choice of orientation, and each slot has exactly its prescribed signed-unit valuation change:
--   $$v\!\left(\prod G_g^1\right)-v\!\left(\prod G_g^0\right)=\begin{cases}e_p,&g\text{ is positive at }p,\\-e_p,&g\text{ is negative at }p.\end{cases}$$
--   Here $v(a)=(v_q(a))_{q\in\mathbb N}$ is the integer valuation vector, and $e_p$ is its coordinate unit vector. Thus the arithmetic marked-path data supply the state-change and collision properties required by the finite universal-bank theorem. The assertion is finite and conditional only on the explicitly stated path and marker data; it does not assert prime supply or joint placement with a fractional selector.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, pinned commit 61325b10bbdc29f4fb5e0618b414b9f2189333ad, Section 5, complete-rough-signature, bank-ordinary-cell, bank-four-bottom-pools, bank-unit-ratio, bank-unit-vector, Lemma bank-donor-injection, and the distinct-marker argument immediately before subsection bank-precharge. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex . See also BankPathAlgebra.lean, BankPaperComponents.lean, and BankPaperExactificationState.lean in 390/lean/Erdos390/WholePaper/.

import Definitions.Def_erdos390_marked_bank_paths
open Erdos390.WholePaper

theorem Erdos390.marked_path_signed_bank_spec
    (P : Finset ℕ) (β : ↑P → ℕ) (R : MarkedBankPaths P β)
    (hprime : ∀ p : ↑P, p.1.Prime) :
    (∀ g b a, a ∈ R.signedState g b → 0 < a) ∧
    (∀ g k, g ≠ k → ∀ b c, Disjoint (R.signedState g b) (R.signedState k c)) ∧
    (∀ g,
      integerValuationVector ((R.signedState g true).prod id) -
          integerValuationVector ((R.signedState g false).prod id) =
        embeddedSignedBankSlotChange (fun p : ↑P ↦ p.1) g) := by sorry
