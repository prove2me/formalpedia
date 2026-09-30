-- Prove2me | solution 1 for lean_workbook_plus_71142
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:20:00.788838+00:00
-- url     : https://prove2.me/submissions/5e29f63b-d6b4-43ac-88e1-f27eeab5b3f0

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

set_option autoImplicit false

namespace ModularSquareOneCount2004

def ringRootEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    {x : R // x ^ 2 = 1} ≃ {x : S // x ^ 2 = 1} where
  toFun x := ⟨e x.1, by rw [← map_pow, x.2, map_one]⟩
  invFun x := ⟨e.symm x.1, by rw [← map_pow, x.2, map_one]⟩
  left_inv x := by apply Subtype.ext; exact e.left_inv x.1
  right_inv x := by apply Subtype.ext; exact e.right_inv x.1

def productRootEquiv {R S : Type*} [Ring R] [Ring S] :
    {x : R × S // x ^ 2 = 1} ≃
      ({x : R // x ^ 2 = 1} × {x : S // x ^ 2 = 1}) where
  toFun x := (⟨x.1.1, congrArg Prod.fst x.2⟩, ⟨x.1.2, congrArg Prod.snd x.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), Prod.ext x.1.2 x.2.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Prod.ext <;> apply Subtype.ext <;> rfl

@[irreducible] def rootCount (n : ℕ) [NeZero n] : ℕ :=
  Fintype.card {x : ZMod n // x ^ 2 = 1}

noncomputable def crtRootEquiv (m n : ℕ) (h : m.Coprime n) :
    {x : ZMod (m * n) // x ^ 2 = 1} ≃
      ({x : ZMod m // x ^ 2 = 1} × {x : ZMod n // x ^ 2 = 1}) :=
  (ringRootEquiv (ZMod.chineseRemainder h)).trans productRootEquiv

theorem root_count_mul (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    rootCount (m * n) = rootCount m * rootCount n := by
  unfold rootCount
  rw [Fintype.card_congr (crtRootEquiv m n h), Fintype.card_prod]

theorem field_root_count {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (h : (1 : K) ≠ -1) : Fintype.card {x : K // x ^ 2 = 1} = 2 := by
  have he : ∀ x : K, x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := fun x => sq_eq_one_iff
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  exact Fintype.card_subtype_eq_or_eq_of_ne h

theorem factor_counts : rootCount 4 = 2 ∧ rootCount 3 = 2 ∧ rootCount 167 = 2 := by
  unfold rootCount
  refine ⟨by decide, ?_, ?_⟩
  · letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact field_root_count (K := ZMod 3) (by decide)
  · letI : Fact (Nat.Prime 167) := ⟨by norm_num⟩
    exact field_root_count (K := ZMod 167) (by decide)

theorem total_count : rootCount 2004 = 8 := by
  have h1 : rootCount 2004 = rootCount 4 * rootCount 501 :=
    root_count_mul 4 501 (by decide)
  have h2 : rootCount 501 = rootCount 3 * rootCount 167 :=
    root_count_mul 3 167 (by decide)
  obtain ⟨h4, h3, h167⟩ := factor_counts
  calc
    rootCount 2004 = rootCount 4 * rootCount 501 := h1
    _ = 2 * (2 * 2) := congrArg₂ Nat.mul h4 (h2.trans (congrArg₂ Nat.mul h3 h167))
    _ = 8 := rfl

def roots : Finset (ZMod 2004) := {1, 335, 667, 1001, 1003, 1337, 1669, 2003}

theorem roots_card : roots.card = 8 := by decide

theorem listed_roots_valid (x : ZMod 2004) (h : x ∈ roots) : x ^ 2 = 1 := by
  simp only [roots, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem roots_eq_all : roots = Finset.univ.filter (fun x : ZMod 2004 => x ^ 2 = 1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, listed_roots_valid x hx⟩
  · have hc := total_count
    unfold rootCount at hc
    rw [Fintype.card_subtype] at hc
    rw [hc, roots_card]

theorem root_classification (x : ZMod 2004) :
    x ^ 2 = 1 ↔ x = 1 ∨ x = 335 ∨ x = 667 ∨ x = 1001 ∨
      x = 1003 ∨ x = 1337 ∨ x = 1669 ∨ x = 2003 := by
  have he : x ^ 2 = 1 ↔ x ∈ roots := by
    rw [roots_eq_all]
    simp
  simpa only [roots, Finset.mem_insert, Finset.mem_singleton] using he

theorem root_set : {x : ZMod 2004 | x ^ 2 = 1} = (↑roots : Set (ZMod 2004)) := by
  rw [roots_eq_all]
  ext x
  simp

theorem root_set_card : {x : ZMod 2004 | x ^ 2 = 1}.ncard = 8 := by
  rw [root_set, Set.ncard_coe_finset, roots_card]

theorem workbook_count_rejected : rootCount 2004 ≠ 4 := by
  rw [total_count]
  norm_num

end ModularSquareOneCount2004

theorem solution : ∃ x : ZMod 2004, x ^ 2 = 1 := by
  exact ⟨1, by ring⟩

#print axioms ModularSquareOneCount2004.ringRootEquiv
#print axioms ModularSquareOneCount2004.productRootEquiv
#print axioms ModularSquareOneCount2004.crtRootEquiv
#print axioms ModularSquareOneCount2004.root_count_mul
#print axioms ModularSquareOneCount2004.field_root_count
#print axioms ModularSquareOneCount2004.factor_counts
#print axioms ModularSquareOneCount2004.total_count
#print axioms ModularSquareOneCount2004.roots_card
#print axioms ModularSquareOneCount2004.listed_roots_valid
#print axioms ModularSquareOneCount2004.roots_eq_all
#print axioms ModularSquareOneCount2004.root_classification
#print axioms ModularSquareOneCount2004.root_set
#print axioms ModularSquareOneCount2004.root_set_card
#print axioms ModularSquareOneCount2004.workbook_count_rejected
#print axioms solution
