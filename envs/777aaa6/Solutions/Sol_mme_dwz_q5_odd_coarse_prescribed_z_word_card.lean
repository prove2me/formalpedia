-- Prove2me | solution 1 for mme_dwz_q5_odd_coarse_prescribed_z_word_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T09:29:31.306149+00:00
-- url     : https://prove2.me/submissions/f1cb3709-9fa1-4436-80cf-171b829ea069

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_prescribed_product_alphabet_word_card
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
open scoped BigOperators
universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace ElementaryWordCard

def coarse (s : Bool) : Fin 5 := if s then 3 else 1
def forbidden (s : Bool) : Fin 3 := if s then 0 else 2
def bitGrade (s : Bool) (a : Fin 2) : Fin 3 := if s then a.succ else a.castSucc

def encode (s : Bool) (x : Fin 2 × Fin 5) : CoarsePair 5 (coarse s) :=
  if hs : s = true then
    if hx : x.1 = 0 then
      ⟨(⟨x.2.val + 1, by omega⟩, 6), by
        subst s
        revert x
        decide +kernel⟩
    else
      ⟨(6, ⟨x.2.val + 1, by omega⟩), by
        subst s
        revert x
        decide +kernel⟩
  else
    if hx : x.1 = 0 then
      ⟨(0, ⟨x.2.val + 1, by omega⟩), by
        have hs' : s = false := by cases s <;> simp_all
        subst s
        simp [coarse, cwSquarePairGrade, cwSquareCoordGrade]
        split_ifs <;> omega⟩
    else
      ⟨(⟨x.2.val + 1, by omega⟩, 0), by
        have hs' : s = false := by cases s <;> simp_all
        subst s
        simp [coarse, cwSquarePairGrade, cwSquareCoordGrade]
        split_ifs <;> omega⟩

theorem encode_bijective (s : Bool) : Function.Bijective (encode s) := by
  cases s <;> decide +kernel

noncomputable def letter (s : Bool) :
    LiftedCoarsePair.{u} 5 (coarse s) ≃ Fin 2 × Fin 5 :=
  Equiv.ulift.trans (Equiv.ofBijective (encode s) (encode_bijective s)).symm

theorem grade_encode (s : Bool) (x : Fin 2 × Fin 5) :
    (encode s x).leftGrade = bitGrade s x.1 := by
  revert x s
  decide +kernel

theorem grade_letter (s : Bool) (x : LiftedCoarsePair.{u} 5 (coarse s)) :
    x.leftGrade = bitGrade s (letter s x).1 := by
  have h : encode s (letter s x) = x.down :=
    (Equiv.ofBijective (encode s) (encode_bijective s)).apply_symm_apply x.down
  change x.down.leftGrade = _
  rw [← h]
  exact grade_encode s (letter s x)

theorem bitGrade_injective (s : Bool) : Function.Injective (bitGrade s) := by
  cases s <;> decide +kernel

theorem bitGrade_ne_forbidden (s : Bool) (a : Fin 2) :
    bitGrade s a ≠ forbidden s := by
  revert a s
  decide +kernel

theorem grade_cases (s : Bool) (a : Fin 3) :
    a = forbidden s ∨ ∃ b : Fin 2, bitGrade s b = a := by
  revert a s
  decide +kernel

theorem count_bit (s : Bool) {n : ℕ}
    (w : PowIndex (LiftedCoarsePair.{u} 5 (coarse s)) n) (a : Fin 2) :
    leftGradeCount LiftedCoarsePair.leftGrade w (bitGrade s a) =
      Fintype.card {r : Fin n // (letter s (PowIndex.get n w r)).1 = a} := by
  classical
  rw [leftGradeCount, Fintype.card_subtype]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, grade_letter]
  exact (bitGrade_injective s).eq_iff

theorem count_forbidden (s : Bool) {n : ℕ}
    (w : PowIndex (LiftedCoarsePair.{u} 5 (coarse s)) n) :
    leftGradeCount LiftedCoarsePair.leftGrade w (forbidden s) = 0 := by
  classical
  unfold leftGradeCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, grade_letter] at hr
  exact bitGrade_ne_forbidden s _ hr

theorem allowed_iff (s : Bool) (p : IntegerZSplitProfile 3)
    (hp : p.count (forbidden s) = 0) (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 5 (coarse s)) (p.length m)) :
    prescribedZWord LiftedCoarsePair.leftGrade p m w ↔
      ∀ a : Fin 2, Fintype.card {r : Fin (p.length m) //
        (letter s (PowIndex.get _ w r)).1 = a} = p.count (bitGrade s a) * m := by
  constructor
  · intro h a
    rw [← count_bit]
    exact h _
  · intro h a
    rcases grade_cases s a with rfl | ⟨b, rfl⟩
    · rw [count_forbidden, hp, zero_mul]
    · rw [count_bit]
      exact h b

theorem bit_count_sum (s : Bool) (p : IntegerZSplitProfile 3)
    (hp : p.count (forbidden s) = 0) (m : ℕ) :
    ∑ a : Fin 2, p.count (bitGrade s a) * m = p.length m := by
  have h : (∑ a : Fin 3, p.count a * m) = p.length m := by
    rw [← Finset.sum_mul, p.count_sum]
    rfl
  cases s <;> simp only [forbidden, Bool.false_eq_true, ↓reduceIte] at hp
  · simpa [bitGrade, Fin.sum_univ_succ, hp] using h
  · simpa [bitGrade, Fin.sum_univ_succ, hp] using h

theorem grade_card (s : Bool) (p : IntegerZSplitProfile 3)
    (hp : p.count (forbidden s) = 0) (m : ℕ) :
    Nat.card {g : Fin (p.length m) → Fin 2 //
      ∀ a, Fintype.card {r // g r = a} = p.count (bitGrade s a) * m} =
      Nat.multinomial Finset.univ (fun a : Fin 3 ↦ p.count a * m) := by
  have hcard := mme_fintype_prescribed_fiber_function_card
    (α := Fin (p.length m)) (ι := Fin 2)
    (fun a ↦ p.count (bitGrade s a) * m)
    (by simpa using bit_count_sum s p hp m)
  rw [Fintype.card_eq_nat_card] at hcard
  rw [hcard, Fintype.card_fin]
  unfold Nat.multinomial
  have hsum : (∑ a : Fin 3, p.count a * m) = p.length m := by
    rw [← Finset.sum_mul, p.count_sum]
    rfl
  rw [hsum]
  congr 1
  cases s <;> simp only [forbidden, Bool.false_eq_true, ↓reduceIte] at hp
  · simp [bitGrade, Fin.prod_univ_succ, hp]
  · simp [bitGrade, Fin.prod_univ_succ, hp]

theorem card (s : Bool) (p : IntegerZSplitProfile 3)
    (hp : p.count (forbidden s) = 0) (m : ℕ) :
    Nat.card {w : PowIndex (LiftedCoarsePair.{u} 5 (coarse s)) (p.length m) //
      prescribedZWord LiftedCoarsePair.leftGrade p m w} =
      Nat.multinomial Finset.univ (fun a : Fin 3 ↦ p.count a * m) *
        5 ^ p.length m := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (allowed_iff s p hp m))]
  rw [mme_prescribed_product_alphabet_word_card
    2 5 (p.length m) (fun a ↦ p.count (bitGrade s a) * m)
    (fun x ↦ (letter s x).1) (letter s) (fun _ ↦ rfl)]
  rw [grade_card s p hp m]

end ElementaryWordCard

theorem solution (p : IntegerZSplitProfile 3) (m : ℕ) :
    (p.count 2 = 0 →
      Nat.card {w : PowIndex (LiftedCoarsePair.{u} 5 1) (p.length m) //
        prescribedZWord LiftedCoarsePair.leftGrade p m w} =
        Nat.multinomial Finset.univ (fun a : Fin 3 ↦ p.count a * m) * 5 ^ p.length m) ∧
    (p.count 0 = 0 →
      Nat.card {w : PowIndex (LiftedCoarsePair.{u} 5 3) (p.length m) //
        prescribedZWord LiftedCoarsePair.leftGrade p m w} =
        Nat.multinomial Finset.univ (fun a : Fin 3 ↦ p.count a * m) * 5 ^ p.length m) := by
  exact ⟨fun hp ↦ ElementaryWordCard.card false p hp m,
    fun hp ↦ ElementaryWordCard.card true p hp m⟩
