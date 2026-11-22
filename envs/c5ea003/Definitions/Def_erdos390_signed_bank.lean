-- Prove2me | Definitions.Def_erdos390_signed_bank
-- name    : erdos390_signed_bank
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-16T14:42:05.974694+00:00
-- url     : https://prove2.me/theorems/1927bd0a-58da-4149-b530-86183e59965d
-- title:
--   Finite signed slots and literal bank state unions
-- statement:
--   For a finite coordinate set $P$ and nonnegative integer capacities $\beta_p$, the signed slots consist of $\beta_p$ positive and $\beta_p$ negative copies at every coordinate. A slot contributes the corresponding signed unit vector when toggled.
--
--   A bank state assigns two finite sets of positive integer factors to each slot. For a Boolean choice $b_g$, define
--   $$B(b)=\bigcup_g G_g^{b_g},\qquad B_0=B(0).$$
--   The prefix choice toggles the first $u_p$ positive copies and the first $v_p$ negative copies. Coordinate vectors are integer-valued functions, embedded into the natural-number prime coordinates by unit vectors.
--
--   These are the finite objects used to turn signed valuation corrections into literal factor-set replacements. Positivity, legal intervals and joint disjointness are hypotheses of the associated theorem, rather than assertions of these definitions.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 5, Lemma precharged-universal-bank; Section 10, equations bank-state-replacement and bank-final-valuation-change. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex . Definitions from BankPathAlgebra.lean, GuardedBankSelection.lean and GuardedExactificationAlgebra.lean.

import Definitions.Def_erdos390_floating_rounding

open scoped BigOperators
namespace Erdos390.WholePaper
noncomputable section

abbrev BankVector (I : Type*) := I → ℤ

/-- The coordinate unit vector at `p`. -/
def coordinateUnit {I : Type*} [DecidableEq I] (p : I) : BankVector I :=
  fun q ↦ if p = q then 1 else 0

/-- The complete integer valuation vector of a natural number. -/
def integerValuationVector (a : ℕ) : BankVector ℕ :=
  fun p ↦ (a.factorization p : ℤ)

abbrev SignedBankSlot {P : Type*} (β : P → ℕ) :=
  Σ p : P, Sum (Fin (β p)) (Fin (β p))

def signedBankSlotChange {P : Type*} [DecidableEq P] {β : P → ℕ}
    (g : SignedBankSlot β) : BankVector P :=
  match g.2 with
  | Sum.inl _ => coordinateUnit g.1
  | Sum.inr _ => -coordinateUnit g.1

/-- Embed a finite coordinate vector into an actual target coordinate type. -/
def embeddedBankVector {P Q : Type*} [Fintype P] [DecidableEq Q]
    (coordinate : P → Q) (z : BankVector P) : BankVector Q :=
  ∑ p : P, (z p) • coordinateUnit (coordinate p)

/-- Actual-coordinate unit change of one signed bank slot. -/
def embeddedSignedBankSlotChange
    {P Q : Type*} [DecidableEq Q] {β : P → ℕ}
    (coordinate : P → Q) (g : SignedBankSlot β) : BankVector Q :=
  match g.2 with
  | Sum.inl _ => coordinateUnit (coordinate g.1)
  | Sum.inr _ => -coordinateUnit (coordinate g.1)

def signedBankStateChoice {P : Type*} {β : P → ℕ}
    (positive negative : P → ℕ) (g : SignedBankSlot β) : Bool :=
  match g.2 with
  | Sum.inl i => decide (i.1 < positive g.1)
  | Sum.inr i => decide (i.1 < negative g.1)

/-- Union of one explicitly chosen state from every concrete path slot. -/
def chosenBankFactors {G : Type*} [Fintype G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion fun g ↦ state g (choice g)

/-- The state-zero bank is a special chosen-state union. -/
def baseBankFactors {G : Type*} [Fintype G]
    (state : G → Bool → Finset ℕ) : Finset ℕ :=
  chosenBankFactors state fun _ ↦ false


end
end Erdos390.WholePaper


