-- Prove2me | solution 1 for Geometry.KernelPatterns.card_patternsWith_eq_stirlingSecond
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T19:06:36.269527+00:00
-- url     : https://prove2.me/submissions/c8393706-7395-4bfe-afb5-5549f31cea21

import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling
import Definitions.Def_Geometry_KernelPatterns_BellRecursion

open Geometry.KernelPatterns Finset in
theorem solution : ∀ n k : ℕ, (patternsWith n k).card = Nat.stirlingSecond n k := by
  classical
  -- Pascal splitting of a binomial sum
  have hpas : ∀ (g : ℕ → ℕ) (m : ℕ), ∑ i ∈ range (m + 2), (m + 1).choose i * g i
      = ∑ i ∈ range (m + 1), m.choose i * g (i + 1) + ∑ i ∈ range (m + 1), m.choose i * g i := by
    intro g m
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ, add_mul, Finset.sum_add_distrib, Nat.choose_zero_right]
    have h1 : ∑ i ∈ range (m + 1), m.choose (i + 1) * g (i + 1)
        = ∑ i ∈ range m, m.choose (i + 1) * g (i + 1) := by
      rw [Finset.sum_range_succ, Nat.choose_succ_self, zero_mul, add_zero]
    have h2 : ∑ i ∈ range (m + 1), m.choose i * g i
        = ∑ i ∈ range m, m.choose (i + 1) * g (i + 1) + 1 * g 0 := by
      rw [Finset.sum_range_succ', Nat.choose_zero_right]
    rw [h1, h2]
    ring
  -- `S(n+1, k+1) = ∑_i C(n, i) S(i, k)`
  have hD : ∀ m k : ℕ, Nat.stirlingSecond (m + 1) (k + 1)
      = ∑ i ∈ range (m + 1), m.choose i * Nat.stirlingSecond i k := by
    intro m
    induction m with
    | zero =>
      intro k
      cases k with
      | zero => simp [Nat.stirlingSecond]
      | succ k => simp [Nat.stirlingSecond]
    | succ m ih =>
      intro k
      rw [hpas (fun i => Nat.stirlingSecond i k) m, ← ih k]
      cases k with
      | zero =>
        simp only [Nat.stirlingSecond_succ_zero, mul_zero, Finset.sum_const_zero, zero_add]
        rw [Nat.stirlingSecond_one_right, Nat.stirlingSecond_one_right]
      | succ k =>
        have hsum : ∑ i ∈ range (m + 1), m.choose i * Nat.stirlingSecond (i + 1) (k + 1)
            = (k + 1) * Nat.stirlingSecond (m + 1) (k + 1 + 1)
              + Nat.stirlingSecond (m + 1) (k + 1) := by
          rw [ih (k + 1), ih k, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Nat.stirlingSecond_succ_succ]
          ring
        rw [hsum, Nat.stirlingSecond_succ_succ (m + 1) (k + 1)]
        ring
  -- image size = number of kernel classes
  have hG : ∀ {m : ℕ} {X : Type} [DecidableEq X] (f : Fin m → X),
      (univ.image f).card = Nat.card (Quotient (Setoid.ker f)) := by
    intro m X _ f
    rw [Nat.card_congr (Setoid.quotientKerEquivRange f), Nat.card_eq_card_toFinset,
      Set.toFinset_range]
  -- the pattern attached to `(S, t)` has one block more than `t`
  have hpatS : ∀ {m : ℕ} (S : Finset (Fin m)) (t : Setoid ↥(Sᶜ)),
      (univ.image (patternOfSetoid S t)).card = Nat.card (Quotient t) + 1 := by
    intro m S t
    rw [hG]
    have hk : Setoid.ker (patternOfSetoid S t) = Setoid.ker (blockFun S t) :=
      Setoid.ext fun a b => patternOfSetoid_eq_iff S t a b
    rw [hk, Nat.card_congr (Setoid.quotientKerEquivRange _)]
    have hsurj : Set.range (blockFun S t) = Set.univ := by
      apply Set.eq_univ_of_forall
      rintro (_ | q)
      · exact ⟨Fin.last m, blockFun_last S t⟩
      · obtain ⟨x, rfl⟩ := Quotient.exists_rep q
        exact ⟨(x : Fin m).castSucc, blockFun_castSucc_of_not_mem t (Finset.mem_compl.1 x.2)⟩
    rw [hsurj, Nat.card_univ, Finite.card_option]
  -- patterns with `k` blocks = setoids with `k` classes
  have hPW : ∀ m k : ℕ, (patternsWith m k).card
      = Nat.card {s : Setoid (Fin m) // Nat.card (Quotient s) = k} := by
    intro m k
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    refine (?_ : ↥(patternsWith m k) ≃ {p : ↥(patterns m m) // (univ.image (p : Fin m → Fin m)).card = k}).trans
      (Equiv.subtypeEquiv (patternsEquivSetoid m) (fun p => ?_))
    · exact { toFun := fun p => ⟨⟨p.1, (Finset.mem_filter.1 p.2).1⟩, (Finset.mem_filter.1 p.2).2⟩
              invFun := fun p => ⟨p.1.1, Finset.mem_filter.2 ⟨p.1.2, p.2⟩⟩
              left_inv := fun p => rfl
              right_inv := fun p => rfl }
    · rw [hG]
      exact Iff.rfl
  -- the fibre over `S` with `k + 1` blocks = setoids on `Sᶜ` with `k` classes
  have hFib : ∀ (m k : ℕ) (S : Finset (Fin m)),
      ((lastBlkFibre m S).filter (fun p => (univ.image p).card = k + 1)).card
        = Nat.card {t : Setoid ↥(Sᶜ) // Nat.card (Quotient t) = k} := by
    intro m k S
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    refine (?_ : ↥((lastBlkFibre m S).filter (fun p => (univ.image p).card = k + 1))
        ≃ {p : ↥(lastBlkFibre m S) // (univ.image (p : Fin (m + 1) → Fin (m + 1))).card = k + 1}).trans
      (Equiv.subtypeEquiv (lastBlkFibreEquiv m S) (fun p => ?_))
    · exact { toFun := fun p => ⟨⟨p.1, (Finset.mem_filter.1 p.2).1⟩, (Finset.mem_filter.1 p.2).2⟩
              invFun := fun p => ⟨p.1.1, Finset.mem_filter.2 ⟨p.1.2, p.2⟩⟩
              left_inv := fun p => rfl
              right_inv := fun p => rfl }
    · have hp : (p : Fin (m + 1) → Fin (m + 1))
          = patternOfSetoid S (lastBlkFibreEquiv m S p) := by
        conv_lhs => rw [← (lastBlkFibreEquiv m S).symm_apply_apply p]
        rfl
      rw [hp, hpatS]
      omega
  -- class counts are invariant under relabelling
  have hTr : ∀ {α β : Type} (e : α ≃ β) (k : ℕ),
      Nat.card {t : Setoid α // Nat.card (Quotient t) = k}
        = Nat.card {t : Setoid β // Nat.card (Quotient t) = k} := by
    intro α β e k
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (setoidCongr e) (fun t => ?_)
    have h : Nat.card (Quotient (setoidCongr e t)) = Nat.card (Quotient t) :=
      Nat.card_congr (Quotient.congr e.symm (fun a b => Iff.rfl))
    rw [h]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    rcases n with _ | m
    · rcases k with _ | k
      · rw [Nat.stirlingSecond_zero, Finset.card_eq_one]
        refine ⟨Fin.elim0, ?_⟩
        ext f
        simp only [Finset.mem_singleton]
        constructor
        · intro _
          funext i
          exact i.elim0
        · rintro rfl
          rw [patternsWith, Finset.mem_filter]
          exact ⟨(mem_patterns_self _).2 (funext fun i => i.elim0), by simp⟩
      · rw [Nat.stirlingSecond_zero_succ, Finset.card_eq_zero, patternsWith,
          Finset.filter_eq_empty_iff]
        intro p _
        simp
    · rcases k with _ | k
      · rw [Nat.stirlingSecond_succ_zero, Finset.card_eq_zero, patternsWith,
          Finset.filter_eq_empty_iff]
        intro p _ h
        have : 0 < (univ.image p).card := Finset.card_pos.2 (Finset.univ_nonempty.image p)
        omega
      · have hfib : (patternsWith (m + 1) (k + 1)).card
            = ∑ S : Finset (Fin m),
                ((lastBlkFibre m S).filter (fun p => (univ.image p).card = k + 1)).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := lastBlk) (t := univ)
            (fun p _ => Finset.mem_coe.2 (Finset.mem_univ (lastBlk p)))]
          refine Finset.sum_congr rfl fun S _ => ?_
          congr 1
          ext p
          simp only [patternsWith, lastBlkFibre, Finset.mem_filter]
          tauto
        have hS : ∀ S : Finset (Fin m),
            ((lastBlkFibre m S).filter (fun p => (univ.image p).card = k + 1)).card
              = (patternsWith (m - S.card) k).card := by
          intro S
          rw [hFib, hTr (Fintype.equivFin ↥(Sᶜ)) k, ← hPW, Fintype.card_coe, Finset.card_compl,
            Fintype.card_fin]
        rw [hfib, Finset.sum_congr rfl fun S _ => hS S,
          Finset.sum_congr rfl fun S _ => ih (m - S.card) (by omega) k,
          ← Finset.powerset_univ,
          Finset.sum_powerset_apply_card (fun j => Nat.stirlingSecond (m - j) k),
          Finset.card_univ, Fintype.card_fin, hD m k]
        conv_rhs => rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [smul_eq_mul, show m + 1 - 1 - j = m - j by omega, Nat.choose_symm (by omega)]
