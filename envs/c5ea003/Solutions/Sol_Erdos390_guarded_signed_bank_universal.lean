-- Prove2me | solution 1 for Erdos390.guarded_signed_bank_universal
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-16T14:47:24.639256+00:00
-- url     : https://prove2.me/submissions/f442c4c9-ab0d-42be-a759-8892b53fdb8c

import Definitions.Def_erdos390_signed_bank
open scoped BigOperators
open Erdos390.WholePaper

/- Adapted from Shouqiao Wang, erdos, commit 61325b10bbdc29f4fb5e0618b414b9f2189333ad:
BankPathAlgebra, GuardedBankSelection and GuardedExactificationAlgebra. -/
namespace Erdos390.WholePaper
noncomputable section

def signedUnitPathChange {I : Type*} [Fintype I] [DecidableEq I]
    (positive negative : I → ℕ) : BankVector I :=
  ∑ p : I, (
    (positive p : ℤ) • coordinateUnit p +
      (negative p : ℤ) • (-coordinateUnit p))

/-- Coordinate evaluation of a finite collection of signed unit paths. -/
theorem signedUnitPathChange_apply {I : Type*} [Fintype I] [DecidableEq I]
    (positive negative : I → ℕ) (q : I) :
    signedUnitPathChange positive negative q =
      (positive q : ℤ) - (negative q : ℤ) := by
  classical
  simp only [signedUnitPathChange, Finset.sum_apply]
  rw [Finset.sum_eq_single q]
  · simp [coordinateUnit, sub_eq_add_neg]
  · intro p _hp hpq
    simp [coordinateUnit, hpq]
  · simp

/-- Positive and negative counts canonically associated with an integral
target coordinate. -/
def positiveUnitPathCount {I : Type*} (z : BankVector I) (p : I) : ℕ :=
  (z p).toNat

def negativeUnitPathCount {I : Type*} (z : BankVector I) (p : I) : ℕ :=
  (-z p).toNat

/-- `β` copies of each signed unit path realize every integral vector in
the coordinate box `|z_p| ≤ β_p`.  The constructed selection in fact uses
only one orientation at each coordinate. -/
theorem twoSidedUnitPaths_boxUniversal
    {I : Type*} [Fintype I] [DecidableEq I]
    (β : I → ℕ) (z : BankVector I)
    (hz : ∀ p, |z p| ≤ (β p : ℤ)) :
    ∃ positive negative : I → ℕ,
      (∀ p, positive p ≤ β p) ∧
      (∀ p, negative p ≤ β p) ∧
      (∀ p, positive p + negative p ≤ β p) ∧
      signedUnitPathChange positive negative = z := by
  refine ⟨positiveUnitPathCount z, negativeUnitPathCount z, ?_, ?_, ?_, ?_⟩
  · intro p
    have hupper : z p ≤ (β p : ℤ) :=
      (le_abs_self (z p)).trans (hz p)
    dsimp only [positiveUnitPathCount]
    omega
  · intro p
    have hupper : -z p ≤ (β p : ℤ) :=
      (neg_le_abs (z p)).trans (hz p)
    dsimp only [negativeUnitPathCount]
    omega
  · intro p
    dsimp only [positiveUnitPathCount, negativeUnitPathCount]
    have habs : (z p).natAbs ≤ β p := by
      have hcast : ((z p).natAbs : ℤ) ≤ (β p : ℤ) := by
        simpa only [Int.natCast_natAbs] using hz p
      exact_mod_cast hcast
    rw [Int.toNat_add_toNat_neg_eq_natAbs]
    exact habs
  · funext p
    rw [signedUnitPathChange_apply]
    dsimp only [positiveUnitPathCount, negativeUnitPathCount]
    exact Int.toNat_sub_toNat_neg (z p)

private theorem card_fin_filter_val_lt {n k : ℕ} (hk : k ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter fun i ↦ i.1 < k).card = k := by
  apply Finset.card_eq_of_bijective
    (fun i hi ↦ (⟨i, lt_of_lt_of_le hi hk⟩ : Fin n))
  · intro a ha
    have ha' : a.1 < k := (Finset.mem_filter.mp ha).2
    exact ⟨a.1, ha', by apply Fin.ext; rfl⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  · intro i j hi hj hij
    exact Fin.ext_iff.mp hij

private theorem sum_fin_if_val_lt
    {V : Type*} [AddCommGroup V] [Module ℤ V]
    {n k : ℕ} (hk : k ≤ n) (v : V) :
    (∑ i : Fin n, if i.1 < k then v else 0) = (k : ℤ) • v := by
  classical
  calc
    (∑ i : Fin n, if i.1 < k then v else 0) =
        ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i ↦ i.1 < k), v := by
      simp only [Finset.sum_filter]
    _ = (((Finset.univ : Finset (Fin n)).filter
          (fun i ↦ i.1 < k)).card : ℤ) • v := by
      simp
    _ = (k : ℤ) • v := by rw [card_fin_filter_val_lt hk]

theorem sum_signedBankSlotChange_of_choice
    {P : Type*} [Fintype P] [DecidableEq P]
    (β positive negative : P → ℕ)
    (hpositive : ∀ p, positive p ≤ β p)
    (hnegative : ∀ p, negative p ≤ β p) :
    (∑ g : SignedBankSlot β,
        if signedBankStateChoice positive negative g then
          signedBankSlotChange g else 0) =
      signedUnitPathChange positive negative := by
  classical
  funext q
  simp only [Fintype.sum_sigma, Fintype.sum_sum_type, Finset.sum_apply,
    signedBankStateChoice, signedBankSlotChange, decide_eq_true_eq,
    signedUnitPathChange, Pi.add_apply, Pi.smul_apply, ite_apply,
    Pi.zero_apply, Pi.neg_apply]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [sum_fin_if_val_lt (hpositive p) (coordinateUnit p q),
    sum_fin_if_val_lt (hnegative p) (-(coordinateUnit p q))]

theorem sum_embeddedSignedBankSlotChange_of_choice
    {P Q : Type*} [Fintype P] [DecidableEq P] [DecidableEq Q]
    (β positive negative : P → ℕ) (coordinate : P → Q)
    (hpositive : ∀ p, positive p ≤ β p)
    (hnegative : ∀ p, negative p ≤ β p) :
    (∑ g : SignedBankSlot β,
        if signedBankStateChoice positive negative g then
          embeddedSignedBankSlotChange coordinate g else 0) =
      embeddedBankVector coordinate
        (signedUnitPathChange positive negative) := by
  classical
  funext q
  simp only [Fintype.sum_sigma, Fintype.sum_sum_type, Finset.sum_apply,
    signedBankStateChoice, embeddedSignedBankSlotChange,
    decide_eq_true_eq, embeddedBankVector,
    Pi.smul_apply, ite_apply, Pi.zero_apply, Pi.neg_apply]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [sum_fin_if_val_lt (hpositive p) (coordinateUnit (coordinate p) q),
    sum_fin_if_val_lt (hnegative p) (-(coordinateUnit (coordinate p) q))]
  rw [signedUnitPathChange_apply]
  ring

theorem exists_bounded_signedBankStateChoice
    {P : Type*} [Fintype P] [DecidableEq P]
    (β : P → ℕ) (z : BankVector P)
    (hz : ∀ p, |z p| ≤ (β p : ℤ)) :
    ∃ positive negative : P → ℕ,
      (∀ p, positive p ≤ β p) ∧
      (∀ p, negative p ≤ β p) ∧
      (∀ p, positive p + negative p ≤ β p) ∧
      (∑ g : SignedBankSlot β,
        if signedBankStateChoice positive negative g then
          signedBankSlotChange g else 0) = z := by
  obtain ⟨positive, negative, hpositive, hnegative, htotal, hchange⟩ :=
    twoSidedUnitPaths_boxUniversal β z hz
  refine ⟨positive, negative, hpositive, hnegative, htotal, ?_⟩
  rw [sum_signedBankSlotChange_of_choice β positive negative
    hpositive hnegative]
  exact hchange

theorem exists_bounded_embeddedBankStateChoice
    {P Q : Type*} [Fintype P] [DecidableEq P] [DecidableEq Q]
    (β : P → ℕ) (coordinate : P → Q) (z : BankVector P)
    (hz : ∀ p, |z p| ≤ (β p : ℤ)) :
    ∃ positive negative : P → ℕ,
      (∀ p, positive p ≤ β p) ∧
      (∀ p, negative p ≤ β p) ∧
      (∀ p, positive p + negative p ≤ β p) ∧
      (∑ g : SignedBankSlot β,
        if signedBankStateChoice positive negative g then
          embeddedSignedBankSlotChange coordinate g else 0) =
        embeddedBankVector coordinate z := by
  obtain ⟨positive, negative, hpositive, hnegative, htotal, hchange⟩ :=
    twoSidedUnitPaths_boxUniversal β z hz
  refine ⟨positive, negative, hpositive, hnegative, htotal, ?_⟩
  rw [sum_embeddedSignedBankSlotChange_of_choice β positive negative
    coordinate hpositive hnegative, hchange]

theorem chosenBankFactors_pairwiseDisjoint
    {G : Type*} [Fintype G] [DecidableEq G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c)) :
    ((Finset.univ : Finset G) : Set G).PairwiseDisjoint
      (fun g ↦ state g (choice g)) := by
  intro g _hg h _hh hne
  exact hcross g h hne (choice g) (choice h)

theorem chosenBankFactors_prod_eq
    {G : Type*} [Fintype G] [DecidableEq G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c)) :
    (chosenBankFactors state choice).prod id =
      ∏ g : G, (state g (choice g)).prod id := by
  classical
  unfold chosenBankFactors
  rw [Finset.prod_biUnion
    (chosenBankFactors_pairwiseDisjoint state choice hcross)]

theorem chosenBankFactors_factorization
    {G : Type*} [Fintype G] [DecidableEq G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (hpositive : ∀ g b a, a ∈ state g b → 0 < a)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c)) (q : ℕ) :
    ((chosenBankFactors state choice).prod id).factorization q =
      ∑ g : G, ((state g (choice g)).prod id).factorization q := by
  rw [chosenBankFactors_prod_eq state choice hcross,
    Nat.factorization_prod_apply]
  intro g _hg
  exact Finset.prod_ne_zero_iff.mpr fun a ha ↦
    (hpositive g (choice g) a ha).ne'

/-- The valuation change of an actually selected bank union is the sum of
the concrete product changes of exactly its toggled slots. -/
theorem chosenBankFactors_factorization_sub_base
    {G : Type*} [Fintype G] [DecidableEq G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (change : G → BankVector ℕ)
    (hpositive : ∀ g b a, a ∈ state g b → 0 < a)
    (hcross : ∀ g h, g ≠ h → ∀ b c,
      Disjoint (state g b) (state h c))
    (hpathChange : ∀ g,
      integerValuationVector ((state g true).prod id) -
          integerValuationVector ((state g false).prod id) = change g)
    (q : ℕ) :
    (((chosenBankFactors state choice).prod id).factorization q : ℤ) -
        (((baseBankFactors state).prod id).factorization q : ℤ) =
      (∑ g : G, if choice g then change g else 0) q := by
  unfold baseBankFactors
  rw [chosenBankFactors_factorization state choice hpositive hcross q,
    chosenBankFactors_factorization state (fun _ ↦ false) hpositive hcross q]
  push_cast
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro g _hg
  cases hchoice : choice g
  · simp
  · simp only [if_true]
    have hgq := congrFun (hpathChange g) q
    exact hgq


end
end Erdos390.WholePaper

theorem solution
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
            embeddedBankVector (fun p : ↑P ↦ p.1) z q := by
  classical
  obtain ⟨positive, negative, hpositiveCount, hnegativeCount, htotal, hsum⟩ :=
    exists_bounded_embeddedBankStateChoice β (fun p : ↑P ↦ p.1) z hz
  refine ⟨positive, negative, htotal, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp ha
    exact hlegal g (signedBankStateChoice positive negative g) hg
  · unfold chosenBankFactors
    rw [Finset.disjoint_biUnion_right]
    intro g _
    exact hguard g (signedBankStateChoice positive negative g)
  · intro q
    have hdelta := chosenBankFactors_factorization_sub_base
      state (signedBankStateChoice positive negative)
      (embeddedSignedBankSlotChange (fun p : ↑P ↦ p.1))
      hpositive hcross hchange q
    rw [hsum] at hdelta
    change integerValuationVector
        ((chosenBankFactors state (signedBankStateChoice positive negative)).prod id) q -
      integerValuationVector ((baseBankFactors state).prod id) q =
        embeddedBankVector (fun p : ↑P ↦ p.1) z q at hdelta
    exact sub_eq_iff_eq_add'.mp hdelta
