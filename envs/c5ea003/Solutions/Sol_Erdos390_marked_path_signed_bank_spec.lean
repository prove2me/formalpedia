-- Prove2me | solution 1 for Erdos390.marked_path_signed_bank_spec
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-16T15:14:37.517059+00:00
-- url     : https://prove2.me/submissions/fe973d90-db93-4305-8198-18b3fb51ee91

import Definitions.Def_erdos390_marked_bank_paths

open scoped BigOperators
open Erdos390.WholePaper

/- Arithmetic specialization of the marked component and path arguments in
Shouqiao Wang, erdos, commit 61325b10bbdc29f4fb5e0618b414b9f2189333ad,
Section 5; BankPathAlgebra.lean and BankPaperExactificationState.lean. -/
namespace Erdos390.WholePaper
noncomputable section

private theorem marked_valuation_prime {p : ℕ} (hp : p.Prime) :
    integerValuationVector p = coordinateUnit p := by
  funext q
  rw [integerValuationVector, hp.factorization]
  by_cases hpq : p = q
  · subst q
    simp [coordinateUnit]
  · simp [coordinateUnit, hpq]

private theorem marked_valuation_one : integerValuationVector 1 = 0 := by
  funext p
  simp [integerValuationVector]

private theorem marked_valuation_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    integerValuationVector (a * b) =
      integerValuationVector a + integerValuationVector b := by
  funext p
  simp only [integerValuationVector, Nat.factorization_mul ha.ne' hb.ne',
    Finsupp.add_apply, Nat.cast_add, Pi.add_apply]

namespace MarkedBankPaths
variable {P : Finset ℕ} {β : ↑P → ℕ} (R : MarkedBankPaths P β)

private theorem cofactor_pos (g : SignedBankSlot β) (b : Bool)
    (i : Fin (R.steps g)) :
    0 < R.scale g i * R.core g (if b then i.1 + 1 else i.1) := by
  apply Nat.mul_pos (R.scale_pos g i)
  cases b
  · exact R.core_pos g i.1 (Nat.le_of_lt i.2)
  · exact R.core_pos g (i.1 + 1) i.2

private theorem cofactor_le (g : SignedBankSlot β) (b : Bool)
    (i : Fin (R.steps g)) :
    R.scale g i * R.core g (if b then i.1 + 1 else i.1) ≤ R.height := by
  cases b
  · exact R.source_small g i
  · exact R.target_small g i

private theorem endpoint_pos (g : SignedBankSlot β) (b : Bool)
    (i : Fin (R.steps g)) : 0 < R.endpoint g b i :=
  Nat.mul_pos (R.marker_prime ⟨g, i⟩).pos (R.cofactor_pos g b i)

/-- A factor recovers its unique large prime marker because its cofactor is smaller. -/
private theorem endpoint_marker_eq
    {g k : SignedBankSlot β} {b c : Bool}
    {i : Fin (R.steps g)} {j : Fin (R.steps k)}
    (heq : R.endpoint g b i = R.endpoint k c j) :
    R.marker ⟨g, i⟩ = R.marker ⟨k, j⟩ := by
  have hd : R.marker ⟨g, i⟩ ∣ R.endpoint k c j := by
    rw [← heq]
    exact dvd_mul_right _ _
  change R.marker ⟨g, i⟩ ∣
    R.marker ⟨k, j⟩ * (R.scale k j * R.core k (if c then j.1 + 1 else j.1)) at hd
  rcases (R.marker_prime ⟨g, i⟩).dvd_mul.mp hd with hmarker | hcofactor
  · exact (((R.marker_prime ⟨k, j⟩).dvd_iff_eq
      (R.marker_prime ⟨g, i⟩).ne_one).mp hmarker).symm
  · have hle := Nat.le_of_dvd (R.cofactor_pos k c j) hcofactor
    exact False.elim ((not_le_of_gt (R.marker_large ⟨g, i⟩))
      (hle.trans (R.cofactor_le k c j)))

private theorem endpoint_injective (g : SignedBankSlot β) (b : Bool) :
    Function.Injective (R.endpoint g b) := by
  intro i j heq
  have hr := R.marker_injective (R.endpoint_marker_eq heq)
  apply Fin.ext
  exact congrArg (fun r : Σ k : SignedBankSlot β, Fin (R.steps k) ↦ r.2.1) hr

private theorem downwardState_pos (g : SignedBankSlot β) (b : Bool)
    {a : ℕ} (ha : a ∈ R.downwardState g b) : 0 < a := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  exact R.endpoint_pos g b i

private theorem downwardState_disjoint
    {g k : SignedBankSlot β} (hne : g ≠ k) (b c : Bool) :
    Disjoint (R.downwardState g b) (R.downwardState k c) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hk
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hk
  have hr := R.marker_injective (R.endpoint_marker_eq (hi.trans hj.symm))
  exact hne (congrArg Sigma.fst hr)

private theorem valuation_downwardState (g : SignedBankSlot β) (b : Bool) :
    integerValuationVector ((R.downwardState g b).prod id) =
      ∑ i : Fin (R.steps g), integerValuationVector (R.endpoint g b i) := by
  classical
  funext q
  simp only [integerValuationVector, Finset.sum_apply]
  rw [Nat.factorization_prod_apply]
  · push_cast
    rw [downwardState, Finset.sum_image]
    rfl
    intro i _ j _ heq
    exact R.endpoint_injective g b heq
  · intro a ha
    exact (R.downwardState_pos g b ha).ne'

private theorem endpoint_change (g : SignedBankSlot β) (i : Fin (R.steps g)) :
    integerValuationVector (R.endpoint g true i) -
        integerValuationVector (R.endpoint g false i) =
      integerValuationVector (R.core g (i.1 + 1)) -
        integerValuationVector (R.core g i.1) := by
  have hp := (R.marker_prime ⟨g, i⟩).pos
  have hs := R.scale_pos g i
  have hc0 := R.core_pos g i.1 (Nat.le_of_lt i.2)
  have hc1 := R.core_pos g (i.1 + 1) i.2
  change integerValuationVector (R.marker ⟨g, i⟩ *
      (R.scale g i * R.core g (i.1 + 1))) -
    integerValuationVector (R.marker ⟨g, i⟩ *
      (R.scale g i * R.core g i.1)) = _
  rw [marked_valuation_mul hp (Nat.mul_pos hs hc1),
    marked_valuation_mul hp (Nat.mul_pos hs hc0),
    marked_valuation_mul hs hc1, marked_valuation_mul hs hc0]
  abel

private theorem downward_change (g : SignedBankSlot β) (hp : g.1.1.Prime) :
    integerValuationVector ((R.downwardState g true).prod id) -
        integerValuationVector ((R.downwardState g false).prod id) =
      -coordinateUnit g.1.1 := by
  rw [R.valuation_downwardState, R.valuation_downwardState,
    ← Finset.sum_sub_distrib]
  simp_rw [R.endpoint_change]
  have hsum :
      (∑ i : Fin (R.steps g),
        (integerValuationVector (R.core g (i.1 + 1)) -
          integerValuationVector (R.core g i.1))) =
      ∑ i ∈ Finset.range (R.steps g),
        (integerValuationVector (R.core g (i + 1)) -
          integerValuationVector (R.core g i)) :=
    (Finset.sum_range (n := R.steps g) (fun i : ℕ ↦
      integerValuationVector (R.core g (i + 1)) -
        integerValuationVector (R.core g i))).symm
  rw [hsum, Finset.sum_range_sub (fun i ↦ integerValuationVector (R.core g i)),
    R.core_finish, R.core_start, marked_valuation_one, marked_valuation_prime hp, zero_sub]

end MarkedBankPaths
end
end Erdos390.WholePaper

theorem solution
    (P : Finset ℕ) (β : ↑P → ℕ) (R : MarkedBankPaths P β)
    (hprime : ∀ p : ↑P, p.1.Prime) :
    (∀ g b a, a ∈ R.signedState g b → 0 < a) ∧
    (∀ g k, g ≠ k → ∀ b c, Disjoint (R.signedState g b) (R.signedState k c)) ∧
    (∀ g,
      integerValuationVector ((R.signedState g true).prod id) -
          integerValuationVector ((R.signedState g false).prod id) =
        embeddedSignedBankSlotChange (fun p : ↑P ↦ p.1) g) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro g b a ha
    rcases g with ⟨p, i | i⟩
    · exact R.downwardState_pos _ (!b) ha
    · exact R.downwardState_pos _ b ha
  · intro g k hne b c
    rcases g with ⟨p, i | i⟩ <;> rcases k with ⟨q, j | j⟩
    · exact R.downwardState_disjoint hne (!b) (!c)
    · exact R.downwardState_disjoint hne (!b) c
    · exact R.downwardState_disjoint hne b (!c)
    · exact R.downwardState_disjoint hne b c
  · intro g
    rcases g with ⟨p, i | i⟩
    · change integerValuationVector ((R.downwardState ⟨p, .inl i⟩ false).prod id) -
          integerValuationVector ((R.downwardState ⟨p, .inl i⟩ true).prod id) =
        coordinateUnit p.1
      calc
        _ = -(integerValuationVector ((R.downwardState ⟨p, .inl i⟩ true).prod id) -
            integerValuationVector ((R.downwardState ⟨p, .inl i⟩ false).prod id)) := by abel
        _ = _ := by rw [R.downward_change _ (hprime p), neg_neg]
    · exact R.downward_change ⟨p, .inr i⟩ (hprime p)
