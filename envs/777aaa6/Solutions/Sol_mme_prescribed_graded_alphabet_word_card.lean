-- Prove2me | solution 1 for mme_prescribed_graded_alphabet_word_card
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T18:41:33.375972+00:00
-- url     : https://prove2.me/submissions/4b5f7a3e-78e1-478b-86c8-ee8a20cd7fee

import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic
open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
open scoped BigOperators
universe u
set_option autoImplicit false
set_option maxHeartbeats 1000000

private noncomputable def wordFibersEquiv
    {I : Type u} [Fintype I] (n t : ℕ) (grade : I → Fin t) (counts : Fin t → ℕ) :
    (Σ g : {g : Fin n → Fin t // ∀ a, Fintype.card {r // g r = a} = counts a},
      (r : Fin n) → {i : I // grade i = g.val r}) ≃
    {w : Fin n → I // ∀ a, Fintype.card {r // grade (w r) = a} = counts a} := by
  classical
  let f : (Σ g : {g : Fin n → Fin t // ∀ a, Fintype.card {r // g r = a} = counts a},
      (r : Fin n) → {i : I // grade i = g.val r}) →
      {w : Fin n → I // ∀ a, Fintype.card {r // grade (w r) = a} = counts a} :=
    fun x ↦ ⟨fun r ↦ (x.2 r).val, by
      intro a
      simp_rw [(x.2 _).property]
      exact x.1.property a⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨g,w⟩ ⟨g',w'⟩ h
    have hw : (fun r ↦ (w r).val) = (fun r ↦ (w' r).val) := congrArg Subtype.val h
    have hg : g = g' := by
      apply Subtype.ext
      funext r
      rw [← (w r).property, ← (w' r).property, congrFun hw r]
    subst g'
    have hww : w = w' := by
      funext r
      exact Subtype.ext (congrFun hw r)
    subst w'
    rfl
  · intro w
    exact ⟨⟨⟨fun r ↦ grade (w.val r), w.property⟩, fun r ↦ ⟨w.val r, rfl⟩⟩, rfl⟩

private theorem fun_word_card
    {I : Type u} [Fintype I] (n t : ℕ) (grade : I → Fin t) (counts : Fin t → ℕ)
    (hsum : ∑ a, counts a = n) :
    Nat.card {w : Fin n → I // ∀ a, Fintype.card {r // grade (w r) = a} = counts a} =
      Nat.multinomial Finset.univ counts *
        ∏ a, (Fintype.card {i : I // grade i = a}) ^ counts a := by
  classical
  rw [← Nat.card_congr (wordFibersEquiv n t grade counts)]
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hp (g : {g : Fin n → Fin t // ∀ a, Fintype.card {r // g r = a} = counts a}) :
      Fintype.card ((r : Fin n) → {i : I // grade i = g.val r}) =
        ∏ a, (Fintype.card {i : I // grade i = a}) ^ counts a := by
    rw [Fintype.card_pi]
    exact (Fintype.prod_fiberwise' g.val (fun a ↦ Fintype.card {i : I // grade i = a})).symm.trans
      (by simp only [Finset.prod_const, Finset.card_univ, g.property])
  simp_rw [hp]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hc := mme_fintype_prescribed_fiber_function_card (α := Fin n) (ι := Fin t) counts (by simpa using hsum)
  have hc' : Fintype.card {g : Fin n → Fin t // ∀ a, Fintype.card {r // g r = a} = counts a} = Nat.multinomial Finset.univ counts := by
    rw [Fintype.card_eq_nat_card] at hc ⊢
    simpa only [Fintype.card_fin, Nat.multinomial, hsum] using hc
  exact congrArg (fun z ↦ z * ∏ a, (Fintype.card {i : I // grade i = a}) ^ counts a) hc'

theorem solution
    {I : Type u} [Fintype I] [DecidableEq I] {t : ℕ}
    (grade : I → Fin t) (p : IntegerZSplitProfile t) (m : ℕ) :
    Nat.card {w : PowIndex I (p.length m) // prescribedZWord grade p m w} =
      Nat.multinomial Finset.univ (fun a ↦ p.count a * m) *
        ∏ a, (Fintype.card {i : I // grade i = a}) ^ (p.count a * m) := by
  classical
  let e : {w : PowIndex I (p.length m) // prescribedZWord grade p m w} ≃
      {w : Fin (p.length m) → I //
        ∀ a, Fintype.card {r // grade (w r) = a} = p.count a * m} :=
    (PowIndex.equivFun I (p.length m)).subtypeEquiv (by
      intro w
      simp only [prescribedZWord, leftGradeCount, Fintype.card_subtype]
      rfl)
  rw [Nat.card_congr e, fun_word_card]
  rw [← Finset.sum_mul, p.count_sum]
  rfl
