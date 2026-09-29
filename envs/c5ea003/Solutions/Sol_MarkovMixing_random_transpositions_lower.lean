-- Prove2me | solution 1 for MarkovMixing.random_transpositions_lower
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T05:47:56.087996+00:00
-- url     : https://prove2.me/submissions/cfb7e13b-ea1a-4d84-8b4f-76d46023895a

import Definitions.Def_mm_shuffle
import Definitions.Def_mm_lower
import Theorems.Thm_MarkovMixing_distinguishing_statistic_nondegenerate
import Theorems.Thm_MarkovMixing_convergence_theorem
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A lower bound for random transpositions (LPW Proposition 8.11)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Counting

variable {n : ℕ}

/-- The number of fixed points. -/
private def fixN (σ : Equiv.Perm (Fin n)) : ℕ :=
  (univ.filter fun i : Fin n => σ i = i).card

private lemma card_shift (ρ : Equiv.Perm (Fin n)) (Q : Equiv.Perm (Fin n) → Prop)
    [DecidablePred Q] :
    (univ.filter fun σ => Q (ρ * σ)).card = (univ.filter Q).card := by
  refine Finset.card_nbij' (fun σ => ρ * σ) (fun σ => ρ⁻¹ * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
    exact hσ
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
    rwa [mul_inv_cancel_left]
  · intro σ _
    simp [inv_mul_cancel_left]
  · intro σ _
    simp [mul_inv_cancel_left]

/-- The number of permutations sending `i` to a given value does not depend on the value. -/
private lemma card_value (i : Fin n) (v w : Fin n) :
    (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = v).card
      = (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = w).card := by
  classical
  have h := card_shift (Equiv.swap v w) (fun σ : Equiv.Perm (Fin n) => σ i = w)
  refine Eq.trans ?_ h
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]
  constructor
  · intro hσ
    rw [hσ, Equiv.swap_apply_left]
  · intro hσ
    have := congrArg (Equiv.swap v w) hσ
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this

private lemma card_perm_eq (hn : 0 < n) (i : Fin n) :
    n * (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card
      = Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm (Fin n) => σ i)
    (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (t := (Finset.univ : Finset (Fin n))) (fun σ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at hfib
  rw [hfib, Finset.sum_congr rfl fun v _ => card_value i v i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private lemma card_pair (i j : Fin n) (hij : i ≠ j) (a b : Fin n) (hab : a ≠ b) :
    (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ j = b).card
      = (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = j).card := by
  classical
  set b' : Fin n := Equiv.swap a i b with hb'
  have hb'i : b' ≠ i := by
    rw [hb']
    intro hc
    have := congrArg (Equiv.swap a i) hc
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    exact hab this.symm
  have step1 : (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ j = b).card
      = (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = b').card := by
    have h := card_shift (Equiv.swap a i)
      (fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = b')
    refine Eq.trans ?_ h
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [h1, Equiv.swap_apply_left]
      · rw [h2, hb']
    · rintro ⟨h1, h2⟩
      constructor
      · have := congrArg (Equiv.swap a i) h1
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      · have := congrArg (Equiv.swap a i) h2
        rw [Equiv.swap_apply_self, hb', Equiv.swap_apply_self] at this
        exact this
  have step2 : (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = b').card
      = (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = j).card := by
    have h := card_shift (Equiv.swap b' j)
      (fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = j)
    refine Eq.trans ?_ h
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]
    have hij' : j ≠ i := fun hc => hij hc.symm
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [h1, Equiv.swap_apply_of_ne_of_ne (Ne.symm hb'i) hij]
      · rw [h2, Equiv.swap_apply_left]
    · rintro ⟨h1, h2⟩
      constructor
      · have := congrArg (Equiv.swap b' j) h1
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne (Ne.symm hb'i) hij] at this
      · have := congrArg (Equiv.swap b' j) h2
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
  rw [step1, step2]

private lemma card_perm_pair (hn : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    n * (n - 1) * (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = j).card
      = Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hmaps : ∀ σ : Equiv.Perm (Fin n), σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))) →
      (σ i, σ j) ∈ (Finset.univ : Finset (Fin n)).offDiag := by
    intro σ _
    rw [Finset.mem_offDiag]
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, fun hc => hij (σ.injective hc)⟩
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm (Fin n) => (σ i, σ j))
    (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (t := (Finset.univ : Finset (Fin n)).offDiag) hmaps
  rw [Finset.card_univ] at hfib
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => (σ i, σ j) = p).card
        = (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = j).card := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    refine Eq.trans ?_ (card_pair i j hij p.1 p.2 hp.2.2)
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
  rw [hfib, Finset.sum_congr rfl hterm, Finset.sum_const, Finset.offDiag_card,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_sub, mul_one]

private lemma sum_fixN (hn : 0 < n) :
    ∑ σ : Equiv.Perm (Fin n), fixN σ = Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hexp : ∀ σ : Equiv.Perm (Fin n),
      fixN σ = ∑ i : Fin n, (if σ i = i then 1 else 0) := by
    intro σ
    rw [fixN, Finset.card_filter]
  rw [Finset.sum_congr rfl fun σ _ => hexp σ, Finset.sum_comm]
  have hin : ∀ i : Fin n,
      (∑ σ : Equiv.Perm (Fin n), if σ i = i then 1 else 0)
        = (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card := by
    intro i
    rw [Finset.card_filter]
  obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [Finset.sum_congr rfl fun i _ => hin i,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      (by
        have h1 := card_perm_eq hn i
        have h2 := card_perm_eq hn i0
        exact Nat.eq_of_mul_eq_mul_left hn (h1.trans h2.symm) :
        (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card
          = (univ.filter fun σ : Equiv.Perm (Fin n) => σ i0 = i0).card)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact card_perm_eq hn i0

private lemma sum_fixN_sq (hn : 2 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n), (fixN σ) ^ 2 = 2 * Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨i0, j0, hij0⟩ : ∃ i0 j0 : Fin n, i0 ≠ j0 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  set B : ℕ := (univ.filter fun σ : Equiv.Perm (Fin n) => σ i0 = i0 ∧ σ j0 = j0).card with hB
  have hnn : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have hBall : ∀ i j : Fin n, i ≠ j →
      (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = j).card = B := by
    intro i j hij
    have h1 := card_perm_pair hn i j hij
    have h2 := card_perm_pair hn i0 j0 hij0
    rw [← hB] at h2
    exact Nat.eq_of_mul_eq_mul_left hnn (h1.trans h2.symm)
  have hcf : ∀ σ : Equiv.Perm (Fin n), fixN σ = ∑ i : Fin n, (if σ i = i then 1 else 0) :=
    fun σ => by rw [fixN, Finset.card_filter]
  have hexp : ∀ σ : Equiv.Perm (Fin n),
      (fixN σ) ^ 2 = ∑ i : Fin n, ∑ j : Fin n, (if σ i = i ∧ σ j = j then 1 else 0) := by
    intro σ
    rw [sq, hcf σ, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : σ i = i
    · by_cases h' : σ j = j
      · rw [if_pos h, if_pos h', if_pos (show σ i = i ∧ σ j = j from ⟨h, h'⟩), mul_one]
      · rw [if_pos h, if_neg h', if_neg (show ¬(σ i = i ∧ σ j = j) from fun hc => h' hc.2),
          mul_zero]
    · rw [if_neg h, if_neg (show ¬(σ i = i ∧ σ j = j) from fun hc => h hc.1), zero_mul]
  rw [Finset.sum_congr rfl fun σ _ => hexp σ, Finset.sum_comm]
  have hswap : ∀ i : Fin n,
      (∑ σ : Equiv.Perm (Fin n), ∑ j : Fin n, (if σ i = i ∧ σ j = j then 1 else 0))
        = ∑ j : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = j).card := by
    intro i
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
  rw [Finset.sum_congr rfl fun i _ => hswap i]
  have hrow : ∀ i : Fin n,
      (∑ j : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i ∧ σ j = j).card)
        = (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card + (n - 1) * B := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_self]
    · rw [Finset.sum_congr rfl fun j hj =>
        hBall i j (fun hc => (Finset.ne_of_mem_erase hj) hc.symm),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
  have h1 : (∑ i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card)
      = Fintype.card (Equiv.Perm (Fin n)) := by
    rw [← sum_fixN hn0, Finset.sum_congr rfl fun σ _ => hcf σ, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.card_filter _ _
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_add_distrib, h1, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← mul_assoc]
  have h2 := card_perm_pair hn i0 j0 hij0
  rw [← hB] at h2
  rw [h2]
  omega


end Counting

section Step

variable {n : ℕ}

private lemma swap_ne_one {i j : Fin n} (hij : i ≠ j) : Equiv.swap i j ≠ (1 : Equiv.Perm (Fin n)) := by
  intro hc
  have := congrArg (fun (e : Equiv.Perm (Fin n)) => e i) hc
  simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at this
  exact hij this.symm

private lemma mem_of_swap_eq {i j a : Fin n} (h : Equiv.swap i j a ≠ a) : a = i ∨ a = j := by
  by_contra hc
  push_neg at hc
  exact h (Equiv.swap_apply_of_ne_of_ne hc.1 hc.2)

private lemma swap_pair {i j a b : Fin n} (hij : i ≠ j) (hab : a ≠ b)
    (h : Equiv.swap i j = Equiv.swap a b) : (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  have ha : a = i ∨ a = j := by
    refine mem_of_swap_eq ?_
    rw [h, Equiv.swap_apply_left]
    exact fun hc => hab hc.symm
  have hb : b = i ∨ b = j := by
    refine mem_of_swap_eq ?_
    rw [h, Equiv.swap_apply_right]
    exact hab
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · exact Or.inl ⟨ha.symm, hb.symm⟩
  · exact Or.inr ⟨hb.symm, ha.symm⟩
  · exact absurd (ha.trans hb.symm) hab

/-- The set of transpositions. -/
private def Tset (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun h : Equiv.Perm (Fin n) => ∃ i j : Fin n, i ≠ j ∧ h = Equiv.swap i j

private lemma one_notMem_Tset : (1 : Equiv.Perm (Fin n)) ∉ Tset n := by
  rw [Tset, Finset.mem_filter]
  rintro ⟨-, i, j, hij, hc⟩
  exact swap_ne_one hij hc.symm

private lemma fiber_card {h : Equiv.Perm (Fin n)} (hh : h ∈ Tset n) :
    ((univ : Finset (Fin n)).offDiag.filter
      fun p : Fin n × Fin n => Equiv.swap p.1 p.2 = h).card = 2 := by
  classical
  rw [Tset, Finset.mem_filter] at hh
  obtain ⟨-, a, b, hab, rfl⟩ := hh
  have hset : ((univ : Finset (Fin n)).offDiag.filter
      fun p : Fin n × Fin n => Equiv.swap p.1 p.2 = Equiv.swap a b) = {(a, b), (b, a)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hq⟩
      rcases swap_pair hp hab hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact Prod.ext h1 h2
      · right; exact Prod.ext h1 h2
    · rintro (rfl | rfl)
      · exact ⟨hab, rfl⟩
      · exact ⟨Ne.symm hab, Equiv.swap_comm b a⟩
  rw [hset, Finset.card_insert_of_notMem
      (by simp only [Finset.mem_singleton, Prod.ext_iff]; rintro ⟨h1, -⟩; exact hab h1),
    Finset.card_singleton]

private lemma sum_offDiag_swap (G : Equiv.Perm (Fin n) → ℝ) :
    ∑ p ∈ (univ : Finset (Fin n)).offDiag, G (Equiv.swap p.1 p.2)
      = 2 * ∑ h ∈ Tset n, G h := by
  classical
  have hmaps : ∀ p ∈ (univ : Finset (Fin n)).offDiag, Equiv.swap p.1 p.2 ∈ Tset n := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    rw [Tset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, p.1, p.2, hp.2.2, rfl⟩
  have hfib := Finset.sum_fiberwise_of_maps_to
    (g := fun p : Fin n × Fin n => Equiv.swap p.1 p.2) hmaps
    (fun p : Fin n × Fin n => G (Equiv.swap p.1 p.2))
  rw [← hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hval : ∀ p ∈ ((univ : Finset (Fin n)).offDiag.filter
      fun p : Fin n × Fin n => Equiv.swap p.1 p.2 = h), G (Equiv.swap p.1 p.2) = G h := by
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, fiber_card hh, nsmul_eq_mul]
  norm_num

private lemma step_eq (hn : 2 ≤ n) (F : Equiv.Perm (Fin n) → ℝ) (σ : Equiv.Perm (Fin n)) :
    ∑ τ : Equiv.Perm (Fin n), randomTranspositions n σ τ * F τ
      = (1 / (n : ℝ)) * F σ
        + (1 / (n : ℝ) ^ 2)
          * ∑ p ∈ (univ : Finset (Fin n)).offDiag, F (Equiv.swap p.1 p.2 * σ) := by
  classical
  have hre : ∑ τ : Equiv.Perm (Fin n), randomTranspositions n σ τ * F τ
      = ∑ h : Equiv.Perm (Fin n), transpositionDist n h * F (h * σ) := by
    rw [← Equiv.sum_comp (Equiv.mulRight σ)
      (fun τ : Equiv.Perm (Fin n) => randomTranspositions n σ τ * F τ)]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [randomTranspositions, groupWalk, mul_inv_cancel_right]
  rw [hre]
  have hzero : ∀ h ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
      h ∉ insert (1 : Equiv.Perm (Fin n)) (Tset n) → transpositionDist n h * F (h * σ) = 0 := by
    intro h _ hh
    rw [Finset.mem_insert] at hh
    push_neg at hh
    have h1 : ¬ (∃ i j : Fin n, i ≠ j ∧ h = Equiv.swap i j) := by
      intro hc
      exact hh.2 (by rw [Tset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc⟩)
    rw [transpositionDist, if_neg hh.1, if_neg h1, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (insert (1 : Equiv.Perm (Fin n)) (Tset n))) hzero]
  rw [Finset.sum_insert one_notMem_Tset]
  have hone : transpositionDist n (1 : Equiv.Perm (Fin n)) * F ((1 : Equiv.Perm (Fin n)) * σ)
      = (1 / (n : ℝ)) * F σ := by
    rw [transpositionDist, if_pos rfl, one_mul]
  have hT : ∀ h ∈ Tset n, transpositionDist n h * F (h * σ)
      = (2 / (n : ℝ) ^ 2) * F (h * σ) := by
    intro h hh
    rw [Tset, Finset.mem_filter] at hh
    obtain ⟨-, i, j, hij, rfl⟩ := hh
    rw [transpositionDist, if_neg (swap_ne_one hij), if_pos ⟨i, j, hij, rfl⟩]
  rw [hone, Finset.sum_congr rfl hT, ← Finset.mul_sum]
  congr 1
  rw [sum_offDiag_swap (fun h => F (h * σ))]
  field_simp
  try ring

end Step


section FixedPoints

variable {n : ℕ}

private def fpR (σ : Equiv.Perm (Fin n)) : ℝ := (fixN σ : ℝ)

private def ggf (σ : Equiv.Perm (Fin n)) : ℝ := fpR σ - 1

private lemma fpR_sum (σ : Equiv.Perm (Fin n)) :
    fpR σ = ∑ i : Fin n, (if σ i = i then (1 : ℝ) else 0) := by
  rw [fpR, fixN, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> norm_num

private lemma sum_offDiag_eq (F : Fin n × Fin n → ℝ) :
    ∑ p ∈ (univ : Finset (Fin n)).offDiag, F p
      = ∑ i : Fin n, ∑ j ∈ univ.erase i, F (i, j) := by
  classical
  have hset : (univ : Finset (Fin n)).offDiag
      = ((univ : Finset (Fin n)) ×ˢ (univ : Finset (Fin n))).filter fun p => p.1 ≠ p.2 := by
    ext p
    simp [Finset.mem_offDiag]
  rw [hset, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  exact ne_comm

private lemma fpR_swap (σ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    fpR (Equiv.swap i j * σ)
      = fpR σ - (if σ i = i then (1 : ℝ) else 0) - (if σ j = j then (1 : ℝ) else 0)
        + (if σ j = i then (1 : ℝ) else 0) + (if σ i = j then (1 : ℝ) else 0) := by
  classical
  have hD : ∀ k : Fin n,
      (if (Equiv.swap i j * σ) k = k then (1 : ℝ) else 0) - (if σ k = k then (1 : ℝ) else 0)
        = (if k = σ⁻¹ i then
            ((if σ j = i then (1 : ℝ) else 0) - (if σ i = i then (1 : ℝ) else 0)) else 0)
          + (if k = σ⁻¹ j then
            ((if σ i = j then (1 : ℝ) else 0) - (if σ j = j then (1 : ℝ) else 0)) else 0) := by
    intro k
    have hki : k = σ⁻¹ i ↔ σ k = i := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [← h]; simp
    have hkj : k = σ⁻¹ j ↔ σ k = j := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [← h]; simp
    by_cases h1 : σ k = i
    · have h2 : ¬ σ k = j := fun hc => hij (h1.symm.trans hc)
      have hnk : ¬ (k = σ⁻¹ j) := fun hc => h2 (hkj.mp hc)
      have p1 : (σ j = i) ↔ (j = k) :=
        ⟨fun h => σ.injective (h.trans h1.symm), fun h => by rw [← h] at h1; exact h1⟩
      have p2 : (σ i = i) ↔ (i = k) :=
        ⟨fun h => σ.injective (h.trans h1.symm), fun h => by rw [← h] at h1; exact h1⟩
      rw [if_pos (hki.mpr h1), if_neg hnk, add_zero]
      simp only [Equiv.Perm.mul_apply, h1, Equiv.swap_apply_left, p1, p2]
    · by_cases h2 : σ k = j
      · have hnk : ¬ (k = σ⁻¹ i) := fun hc => h1 (hki.mp hc)
        have p1 : (σ i = j) ↔ (i = k) :=
          ⟨fun h => σ.injective (h.trans h2.symm), fun h => by rw [← h] at h2; exact h2⟩
        have p2 : (σ j = j) ↔ (j = k) :=
          ⟨fun h => σ.injective (h.trans h2.symm), fun h => by rw [← h] at h2; exact h2⟩
        rw [if_neg hnk, if_pos (hkj.mpr h2), zero_add]
        simp only [Equiv.Perm.mul_apply, h2, Equiv.swap_apply_right, p1, p2]
      · rw [if_neg (fun hc => h1 (hki.mp hc)), if_neg (fun hc => h2 (hkj.mp hc))]
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
        ring
  have hsum : ∑ k : Fin n,
      ((if (Equiv.swap i j * σ) k = k then (1 : ℝ) else 0) - (if σ k = k then (1 : ℝ) else 0))
      = ((if σ j = i then (1 : ℝ) else 0) - (if σ i = i then (1 : ℝ) else 0))
        + ((if σ i = j then (1 : ℝ) else 0) - (if σ j = j then (1 : ℝ) else 0)) := by
    rw [Finset.sum_congr rfl fun k _ => hD k, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (σ⁻¹ i), Finset.sum_ite_eq' Finset.univ (σ⁻¹ j)]
    simp
  rw [Finset.sum_sub_distrib, ← fpR_sum, ← fpR_sum] at hsum
  linarith

end FixedPoints


section Steps

variable {n : ℕ}

private lemma sum_one_row (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (∑ j : Fin n, (if σ j = i then (1 : ℝ) else 0)) = 1 := by
  have h : ∀ j : Fin n, (if σ j = i then (1 : ℝ) else 0) = (if j = σ⁻¹ i then (1:ℝ) else 0) := by
    intro j
    congr 1
    simp only [eq_iff_iff]
    constructor
    · intro hj; rw [← hj]; simp
    · intro hj; rw [hj]; simp
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_eq' Finset.univ (σ⁻¹ i)]
  simp

private lemma sum_one_col (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (∑ j : Fin n, (if σ i = j then (1 : ℝ) else 0)) = 1 := by
  rw [Finset.sum_congr rfl fun j _ => (by
    congr 1
    simp only [eq_iff_iff]
    exact eq_comm : (if σ i = j then (1 : ℝ) else 0) = (if j = σ i then (1:ℝ) else 0)),
    Finset.sum_ite_eq' Finset.univ (σ i)]
  simp

private lemma erase_sum (F : Fin n → ℝ) (i : Fin n) :
    (∑ j ∈ univ.erase i, F j) = (∑ j : Fin n, F j) - F i := by
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ i)]
  ring

private lemma sum_off_1 (σ : Equiv.Perm (Fin n)) :
    ∑ p ∈ (univ : Finset (Fin n)).offDiag, (if σ p.1 = p.1 then (1 : ℝ) else 0)
      = ((n : ℝ) - 1) * fpR σ := by
  rw [sum_offDiag_eq]
  have h : ∀ i : Fin n, (∑ j ∈ univ.erase i, (if σ i = i then (1 : ℝ) else 0))
      = ((n : ℝ) - 1) * (if σ i = i then (1 : ℝ) else 0) := by
    intro i
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    congr 1
    have : (1 : ℕ) ≤ n := Fin.pos i
    push_cast [Nat.cast_sub this]
    ring
  rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.mul_sum, ← fpR_sum]

private lemma sum_off_2 (σ : Equiv.Perm (Fin n)) :
    ∑ p ∈ (univ : Finset (Fin n)).offDiag, (if σ p.2 = p.2 then (1 : ℝ) else 0)
      = ((n : ℝ) - 1) * fpR σ := by
  rw [sum_offDiag_eq]
  have h : ∀ i : Fin n, (∑ j ∈ univ.erase i, (if σ j = j then (1 : ℝ) else 0))
      = fpR σ - (if σ i = i then (1 : ℝ) else 0) := by
    intro i
    rw [erase_sum, ← fpR_sum]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← fpR_sum]
  ring

private lemma sum_off_3 (σ : Equiv.Perm (Fin n)) :
    ∑ p ∈ (univ : Finset (Fin n)).offDiag, (if σ p.2 = p.1 then (1 : ℝ) else 0)
      = (n : ℝ) - fpR σ := by
  rw [sum_offDiag_eq]
  have h : ∀ i : Fin n, (∑ j ∈ univ.erase i, (if σ j = i then (1 : ℝ) else 0))
      = 1 - (if σ i = i then (1 : ℝ) else 0) := by
    intro i
    rw [erase_sum, sum_one_row]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← fpR_sum]

private lemma sum_off_4 (σ : Equiv.Perm (Fin n)) :
    ∑ p ∈ (univ : Finset (Fin n)).offDiag, (if σ p.1 = p.2 then (1 : ℝ) else 0)
      = (n : ℝ) - fpR σ := by
  rw [sum_offDiag_eq]
  have h : ∀ i : Fin n, (∑ j ∈ univ.erase i, (if σ i = j then (1 : ℝ) else 0))
      = 1 - (if σ i = i then (1 : ℝ) else 0) := by
    intro i
    rw [erase_sum, sum_one_col]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← fpR_sum]

private lemma sum_off_5 (σ : Equiv.Perm (Fin n)) :
    ∑ p ∈ (univ : Finset (Fin n)).offDiag,
        (if σ p.1 = p.1 then (1 : ℝ) else 0) * (if σ p.2 = p.2 then (1 : ℝ) else 0)
      = fpR σ ^ 2 - fpR σ := by
  rw [sum_offDiag_eq]
  have h : ∀ i : Fin n,
      (∑ j ∈ univ.erase i,
        (if σ i = i then (1 : ℝ) else 0) * (if σ j = j then (1 : ℝ) else 0))
        = (if σ i = i then (1 : ℝ) else 0) * fpR σ
          - (if σ i = i then (1 : ℝ) else 0) := by
    intro i
    rw [← Finset.mul_sum, erase_sum, ← fpR_sum]
    by_cases hc : σ i = i
    · rw [if_pos hc]; ring
    · rw [if_neg hc]; ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, ← Finset.sum_mul, ← fpR_sum]
  ring

private lemma sum_off_6_nonneg (σ : Equiv.Perm (Fin n)) :
    0 ≤ ∑ p ∈ (univ : Finset (Fin n)).offDiag,
        (if σ p.2 = p.1 then (1 : ℝ) else 0) * (if σ p.1 = p.2 then (1 : ℝ) else 0) := by
  refine Finset.sum_nonneg fun p _ => ?_
  positivity

private lemma sum_off_6_le (σ : Equiv.Perm (Fin n)) :
    (∑ p ∈ (univ : Finset (Fin n)).offDiag,
        (if σ p.2 = p.1 then (1 : ℝ) else 0) * (if σ p.1 = p.2 then (1 : ℝ) else 0))
      ≤ (n : ℝ) - fpR σ := by
  rw [← sum_off_4]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases h1 : σ p.2 = p.1
  · rw [if_pos h1, one_mul]
  · rw [if_neg h1, zero_mul]
    split_ifs <;> norm_num

private lemma offDiag_card_real (hn : 1 ≤ n) :
    (((univ : Finset (Fin n)).offDiag.card : ℕ) : ℝ) = (n : ℝ) ^ 2 - (n : ℝ) := by
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  have hle : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  push_cast [Nat.cast_sub hle]
  ring

private lemma sum_expand5 (A : ℝ) (B C D E : Fin n × Fin n → ℝ) :
    ∑ p ∈ (univ : Finset (Fin n)).offDiag, (A - B p - C p + D p + E p)
      = (((univ : Finset (Fin n)).offDiag.card : ℕ) : ℝ) * A
        - (∑ p ∈ (univ : Finset (Fin n)).offDiag, B p)
        - (∑ p ∈ (univ : Finset (Fin n)).offDiag, C p)
        + (∑ p ∈ (univ : Finset (Fin n)).offDiag, D p)
        + ∑ p ∈ (univ : Finset (Fin n)).offDiag, E p := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

private lemma ggf_swap (σ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    ggf (Equiv.swap i j * σ)
      = ggf σ - (if σ i = i then (1 : ℝ) else 0) - (if σ j = j then (1 : ℝ) else 0)
        + (if σ j = i then (1 : ℝ) else 0) + (if σ i = j then (1 : ℝ) else 0) := by
  rw [ggf, ggf, fpR_swap σ hij]
  ring

private lemma step_g (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    ∑ τ : Equiv.Perm (Fin n), randomTranspositions n σ τ * ggf τ
      = (1 - 2 / (n : ℝ)) * ggf σ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [step_eq hn ggf σ]
  have hpt : ∀ p ∈ (univ : Finset (Fin n)).offDiag,
      ggf (Equiv.swap p.1 p.2 * σ)
        = ggf σ - (if σ p.1 = p.1 then (1 : ℝ) else 0)
            - (if σ p.2 = p.2 then (1 : ℝ) else 0)
          + (if σ p.2 = p.1 then (1 : ℝ) else 0)
          + (if σ p.1 = p.2 then (1 : ℝ) else 0) := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    exact ggf_swap σ hp.2.2
  rw [Finset.sum_congr rfl hpt, sum_expand5, sum_off_1, sum_off_2, sum_off_3, sum_off_4,
    offDiag_card_real (by omega)]
  have hg : fpR σ = ggf σ + 1 := by rw [ggf]; ring
  rw [hg]
  field_simp
  ring

private lemma step_g2 (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    ∑ τ : Equiv.Perm (Fin n), randomTranspositions n σ τ * (ggf τ) ^ 2
      ≤ (1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) * (ggf σ) ^ 2
        + ((2 * (n : ℝ) - 4) * ggf σ + (6 * (n : ℝ) - 6)) / (n : ℝ) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [step_eq hn (fun τ => (ggf τ) ^ 2) σ]
  set S6 : ℝ := ∑ p ∈ (univ : Finset (Fin n)).offDiag,
      (if σ p.2 = p.1 then (1 : ℝ) else 0) * (if σ p.1 = p.2 then (1 : ℝ) else 0) with hS6
  have hpt : ∀ p ∈ (univ : Finset (Fin n)).offDiag,
      (ggf (Equiv.swap p.1 p.2 * σ)) ^ 2
        = (ggf σ) ^ 2
          + 2 * ggf σ * ((if σ p.2 = p.1 then (1 : ℝ) else 0)
              + (if σ p.1 = p.2 then (1 : ℝ) else 0)
              - (if σ p.1 = p.1 then (1 : ℝ) else 0)
              - (if σ p.2 = p.2 then (1 : ℝ) else 0))
          + ((if σ p.1 = p.1 then (1 : ℝ) else 0) + (if σ p.2 = p.2 then (1 : ℝ) else 0)
              + (if σ p.2 = p.1 then (1 : ℝ) else 0) + (if σ p.1 = p.2 then (1 : ℝ) else 0)
              + 2 * ((if σ p.1 = p.1 then (1 : ℝ) else 0)
                    * (if σ p.2 = p.2 then (1 : ℝ) else 0))
              + 2 * ((if σ p.2 = p.1 then (1 : ℝ) else 0)
                    * (if σ p.1 = p.2 then (1 : ℝ) else 0))) := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    have hij := hp.2.2
    set u : ℝ := if σ p.1 = p.1 then (1 : ℝ) else 0 with hu
    set v : ℝ := if σ p.2 = p.2 then (1 : ℝ) else 0 with hv
    set w : ℝ := if σ p.2 = p.1 then (1 : ℝ) else 0 with hw
    set z : ℝ := if σ p.1 = p.2 then (1 : ℝ) else 0 with hz
    have hu2 : u ^ 2 = u := by rw [hu]; split_ifs <;> norm_num
    have hv2 : v ^ 2 = v := by rw [hv]; split_ifs <;> norm_num
    have hw2 : w ^ 2 = w := by rw [hw]; split_ifs <;> norm_num
    have hz2 : z ^ 2 = z := by rw [hz]; split_ifs <;> norm_num
    have huw : u * w = 0 := by
      rw [hu, hw]
      by_cases h1 : σ p.1 = p.1
      · rw [if_pos h1, one_mul, if_neg (fun h2 => hij (σ.injective (h1.trans h2.symm)))]
      · rw [if_neg h1, zero_mul]
    have huz : u * z = 0 := by
      rw [hu, hz]
      by_cases h1 : σ p.1 = p.1
      · rw [if_pos h1, one_mul, if_neg (fun h2 => hij (h1.symm.trans h2))]
      · rw [if_neg h1, zero_mul]
    have hvw : v * w = 0 := by
      rw [hv, hw]
      by_cases h1 : σ p.2 = p.2
      · rw [if_pos h1, one_mul, if_neg (fun h2 => hij (h2.symm.trans h1))]
      · rw [if_neg h1, zero_mul]
    have hvz : v * z = 0 := by
      rw [hv, hz]
      by_cases h1 : σ p.2 = p.2
      · rw [if_pos h1, one_mul, if_neg (fun h2 => hij (σ.injective (h2.trans h1.symm)))]
      · rw [if_neg h1, zero_mul]
    rw [ggf_swap σ hij, ← hu, ← hv, ← hw, ← hz]
    linear_combination hw2 + hz2 + hu2 + hv2 - 2 * huw - 2 * hvw - 2 * huz - 2 * hvz
  rw [Finset.sum_congr rfl hpt]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  rw [sum_off_1, sum_off_2, sum_off_3, sum_off_4, sum_off_5, ← hS6,
    offDiag_card_real (by omega : 1 ≤ n)]
  have hS6le := sum_off_6_le σ
  have hS6nn := sum_off_6_nonneg σ
  rw [← hS6] at hS6le hS6nn
  have hg : fpR σ = ggf σ + 1 := by rw [ggf]; ring
  rw [hg] at hS6le ⊢
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hn2
  have e1 : (n : ℝ) ^ 2 * (1 / (n : ℝ) * ggf σ ^ 2
      + 1 / (n : ℝ) ^ 2 * (((n : ℝ) ^ 2 - (n : ℝ)) * ggf σ ^ 2
          + 2 * ggf σ * ((n : ℝ) - (ggf σ + 1) + ((n : ℝ) - (ggf σ + 1))
              - ((n : ℝ) - 1) * (ggf σ + 1) - ((n : ℝ) - 1) * (ggf σ + 1))
          + (((n : ℝ) - 1) * (ggf σ + 1) + ((n : ℝ) - 1) * (ggf σ + 1)
              + ((n : ℝ) - (ggf σ + 1)) + ((n : ℝ) - (ggf σ + 1))
              + 2 * ((ggf σ + 1) ^ 2 - (ggf σ + 1)) + 2 * S6)))
      = (n : ℝ) * ggf σ ^ 2 + (((n : ℝ) ^ 2 - (n : ℝ)) * ggf σ ^ 2
          - 4 * (n : ℝ) * ggf σ ^ 2
          + (2 * ggf σ ^ 2 + 2 * (n : ℝ) * ggf σ - 2 * ggf σ + 4 * (n : ℝ) - 4 + 2 * S6)) := by
    field_simp
    ring
  have e2 : (n : ℝ) ^ 2 * ((1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) * ggf σ ^ 2
      + ((2 * (n : ℝ) - 4) * ggf σ + (6 * (n : ℝ) - 6)) / (n : ℝ) ^ 2)
      = (n : ℝ) ^ 2 * ggf σ ^ 2 - 4 * (n : ℝ) * ggf σ ^ 2 + 2 * ggf σ ^ 2
        + ((2 * (n : ℝ) - 4) * ggf σ + (6 * (n : ℝ) - 6)) := by
    field_simp
    try ring
  rw [e1, e2]
  linarith [hS6le]



end Steps


section Moments

variable {n : ℕ}

private lemma rt_nonneg (σ τ : Equiv.Perm (Fin n)) : 0 ≤ randomTranspositions n σ τ := by
  rw [randomTranspositions, groupWalk, transpositionDist]
  split_ifs <;> positivity

private lemma rt_stochastic (hn : 2 ≤ n) : IsStochastic (randomTranspositions n) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  refine ⟨rt_nonneg, fun σ => ?_⟩
  have h := step_eq hn (fun _ => (1 : ℝ)) σ
  simp only [mul_one] at h
  rw [h, Finset.sum_const, nsmul_eq_mul, mul_one, offDiag_card_real (by omega : 1 ≤ n)]
  field_simp
  ring

private lemma pow_nonneg_rt (hn : 2 ≤ n) :
    ∀ (t : ℕ) (x y : Equiv.Perm (Fin n)), 0 ≤ ((randomTranspositions n) ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (rt_nonneg z y)

private lemma pow_sum_rt (hn : 2 ≤ n) :
    ∀ (t : ℕ) (x : Equiv.Perm (Fin n)), ∑ y, ((randomTranspositions n) ^ t) x y = 1 := by
  intro t
  induction t with
  | zero => intro x; simp [Matrix.one_apply]
  | succ t ih =>
      intro x
      rw [Finset.sum_congr rfl fun y _ => by rw [pow_succ, Matrix.mul_apply], Finset.sum_comm]
      rw [Finset.sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm]
      rw [Finset.sum_congr rfl fun z _ => by rw [(rt_stochastic hn).2 z, mul_one]]
      exact ih x

private lemma tower (hn : 2 ≤ n) (t : ℕ) (x : Equiv.Perm (Fin n))
    (F : Equiv.Perm (Fin n) → ℝ) :
    ∑ τ, ((randomTranspositions n) ^ (t + 1)) x τ * F τ
      = ∑ σ, ((randomTranspositions n) ^ t) x σ * (∑ τ, randomTranspositions n σ τ * F τ) := by
  rw [Finset.sum_congr rfl fun τ _ => by rw [pow_succ, Matrix.mul_apply, Finset.sum_mul],
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun τ _ => by ring

private def mom1 (n : ℕ) (t : ℕ) : ℝ :=
  ∑ τ : Equiv.Perm (Fin n), ((randomTranspositions n) ^ t) 1 τ * ggf τ

private def mom2 (n : ℕ) (t : ℕ) : ℝ :=
  ∑ τ : Equiv.Perm (Fin n), ((randomTranspositions n) ^ t) 1 τ * (ggf τ) ^ 2

private lemma fixN_one (n : ℕ) : fixN (1 : Equiv.Perm (Fin n)) = n := by
  rw [fixN]
  have : (univ.filter fun i : Fin n => (1 : Equiv.Perm (Fin n)) i = i) = univ := by
    ext i; simp
  rw [this, Finset.card_univ, Fintype.card_fin]

private lemma mom1_eq (hn : 2 ≤ n) (t : ℕ) :
    mom1 n t = ((n : ℝ) - 1) * (1 - 2 / (n : ℝ)) ^ t := by
  induction t with
  | zero =>
      rw [mom1, pow_zero, pow_zero, mul_one]
      have hs : ∀ τ : Equiv.Perm (Fin n),
          ((1 : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℝ) 1 τ) * ggf τ
            = if (1 : Equiv.Perm (Fin n)) = τ then ggf τ else 0 := by
        intro τ
        rw [Matrix.one_apply]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun τ _ => hs τ,
        Finset.sum_ite_eq Finset.univ (1 : Equiv.Perm (Fin n)) ggf, if_pos (Finset.mem_univ _),
        ggf, fpR, fixN_one]
  | succ t ih =>
      rw [mom1, tower hn]
      have hstep : ∀ σ : Equiv.Perm (Fin n),
          ((randomTranspositions n) ^ t) 1 σ * (∑ τ, randomTranspositions n σ τ * ggf τ)
            = (1 - 2 / (n : ℝ)) * (((randomTranspositions n) ^ t) 1 σ * ggf σ) := by
        intro σ
        rw [step_g hn σ]
        ring
      rw [Finset.sum_congr rfl fun σ _ => hstep σ, ← Finset.mul_sum, ← mom1, ih]
      ring


private lemma mom2_le (hn : 4 ≤ n) (t : ℕ) :
    mom2 n t ≤ (1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) ^ t * ((n : ℝ) - 1) ^ 2
      + ((2 * (n : ℝ) - 4) / (2 * (n : ℝ) - 2)) * mom1 n t
      + (6 * (n : ℝ) - 6) / (4 * (n : ℝ) - 2) := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnu0 : (0 : ℝ) ≤ 1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2 := by
    have h : 1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2
        = ((n : ℝ) ^ 2 - 4 * (n : ℝ) + 2) / (n : ℝ) ^ 2 := by field_simp; try ring
    rw [h]
    apply div_nonneg _ (by positivity)
    nlinarith
  induction t with
  | zero =>
      have h1 : mom1 n 0 = (n : ℝ) - 1 := by rw [mom1_eq hn2 0]; ring
      have h2 : mom2 n 0 = ((n : ℝ) - 1) ^ 2 := by
        rw [mom2, pow_zero]
        have hs : ∀ τ : Equiv.Perm (Fin n),
            ((1 : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℝ) 1 τ) * (ggf τ) ^ 2
              = if (1 : Equiv.Perm (Fin n)) = τ then (ggf τ) ^ 2 else 0 := by
          intro τ
          rw [Matrix.one_apply]
          split_ifs <;> ring
        rw [Finset.sum_congr rfl fun τ _ => hs τ,
          Finset.sum_ite_eq Finset.univ (1 : Equiv.Perm (Fin n)) (fun τ => (ggf τ) ^ 2),
          if_pos (Finset.mem_univ _), ggf, fpR, fixN_one]
      rw [h1, h2, pow_zero, one_mul]
      have hc1 : (0 : ℝ) ≤ (2 * (n : ℝ) - 4) / (2 * (n : ℝ) - 2) := by
        apply div_nonneg <;> linarith
      have hc2 : (0 : ℝ) ≤ (6 * (n : ℝ) - 6) / (4 * (n : ℝ) - 2) := by
        apply div_nonneg <;> linarith
      nlinarith [hc1, hc2, hn4]
  | succ t ih =>
      have hrec : mom2 n (t + 1)
          ≤ (1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) * mom2 n t
            + ((2 * (n : ℝ) - 4) * mom1 n t + (6 * (n : ℝ) - 6)) / (n : ℝ) ^ 2 := by
        rw [mom2, tower hn2]
        have hb : ∀ σ : Equiv.Perm (Fin n),
            ((randomTranspositions n) ^ t) 1 σ * (∑ τ, randomTranspositions n σ τ * (ggf τ) ^ 2)
              ≤ ((randomTranspositions n) ^ t) 1 σ
                * ((1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) * (ggf σ) ^ 2
                   + ((2 * (n : ℝ) - 4) * ggf σ + (6 * (n : ℝ) - 6)) / (n : ℝ) ^ 2) := by
          intro σ
          exact mul_le_mul_of_nonneg_left (step_g2 hn2 σ) (pow_nonneg_rt hn2 t 1 σ)
        refine le_trans (Finset.sum_le_sum fun σ _ => hb σ) ?_
        have hexp : ∀ σ : Equiv.Perm (Fin n),
            ((randomTranspositions n) ^ t) 1 σ
              * ((1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) * (ggf σ) ^ 2
                 + ((2 * (n : ℝ) - 4) * ggf σ + (6 * (n : ℝ) - 6)) / (n : ℝ) ^ 2)
              = (1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2)
                  * (((randomTranspositions n) ^ t) 1 σ * (ggf σ) ^ 2)
                + ((2 * (n : ℝ) - 4) / (n : ℝ) ^ 2)
                  * (((randomTranspositions n) ^ t) 1 σ * ggf σ)
                + ((6 * (n : ℝ) - 6) / (n : ℝ) ^ 2) * (((randomTranspositions n) ^ t) 1 σ) := by
          intro σ
          field_simp
          ring
        rw [Finset.sum_congr rfl fun σ _ => hexp σ, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← mom2, ← mom1,
          pow_sum_rt hn2 t 1, mul_one]
        rw [add_div]
        refine le_of_eq ?_
        ring
      refine le_trans hrec ?_
      have hstep := mul_le_mul_of_nonneg_left ih hnu0
      have hc1id : (1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) * ((2 * (n : ℝ) - 4) / (2 * (n : ℝ) - 2))
            + (2 * (n : ℝ) - 4) / (n : ℝ) ^ 2
          = ((2 * (n : ℝ) - 4) / (2 * (n : ℝ) - 2)) * (1 - 2 / (n : ℝ)) := by
        have h1 : (2 * (n : ℝ) - 2) ≠ 0 := by intro hc; nlinarith
        have h1' : ((n : ℝ) - 1) ≠ 0 := by intro hc; nlinarith
        field_simp
        ring
      have hc2id : (1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) * ((6 * (n : ℝ) - 6) / (4 * (n : ℝ) - 2))
            + (6 * (n : ℝ) - 6) / (n : ℝ) ^ 2
          = (6 * (n : ℝ) - 6) / (4 * (n : ℝ) - 2) := by
        have h1 : (4 * (n : ℝ) - 2) ≠ 0 := by intro hc; nlinarith
        have h1' : (2 * (n : ℝ) - 1) ≠ 0 := by intro hc; nlinarith
        field_simp
        ring
      have hkey : (1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2)
            * ((1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) ^ t * ((n : ℝ) - 1) ^ 2
              + ((2 * (n : ℝ) - 4) / (2 * (n : ℝ) - 2)) * mom1 n t
              + (6 * (n : ℝ) - 6) / (4 * (n : ℝ) - 2))
            + ((2 * (n : ℝ) - 4) * mom1 n t + (6 * (n : ℝ) - 6)) / (n : ℝ) ^ 2
          = (1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) ^ (t + 1) * ((n : ℝ) - 1) ^ 2
            + ((2 * (n : ℝ) - 4) / (2 * (n : ℝ) - 2)) * ((1 - 2 / (n : ℝ)) * mom1 n t)
            + (6 * (n : ℝ) - 6) / (4 * (n : ℝ) - 2) := by
        rw [pow_succ]
        linear_combination (mom1 n t) * hc1id + hc2id
      have hm1 : mom1 n (t + 1) = (1 - 2 / (n : ℝ)) * mom1 n t := by
        rw [mom1_eq hn2, mom1_eq hn2]
        ring
      rw [hm1]
      linarith [hstep, hkey]

private lemma var_le (hn : 4 ≤ n) (t : ℕ) :
    mom2 n t - (mom1 n t) ^ 2
      ≤ ((2 * (n : ℝ) - 4) / (2 * (n : ℝ) - 2)) * mom1 n t
        + (6 * (n : ℝ) - 6) / (4 * (n : ℝ) - 2) := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnu0 : (0 : ℝ) ≤ 1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2 := by
    have h : 1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2
        = ((n : ℝ) ^ 2 - 4 * (n : ℝ) + 2) / (n : ℝ) ^ 2 := by field_simp; try ring
    rw [h]
    apply div_nonneg _ (by positivity)
    nlinarith
  have hle : 1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2 ≤ (1 - 2 / (n : ℝ)) ^ 2 := by
    have h : (1 - 2 / (n : ℝ)) ^ 2 = 1 - 4 / (n : ℝ) + 4 / (n : ℝ) ^ 2 := by
      field_simp
      ring
    rw [h]
    have hpos2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have h2 : (2 : ℝ) / (n : ℝ) ^ 2 ≤ 4 / (n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hpos2 hpos2]
      nlinarith
    linarith
  have hpow : (1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) ^ t * ((n : ℝ) - 1) ^ 2 ≤ (mom1 n t) ^ 2 := by
    rw [mom1_eq hn2, mul_pow, ← pow_mul, mul_comm t 2, pow_mul]
    have h1 : (1 - 4 / (n : ℝ) + 2 / (n : ℝ) ^ 2) ^ t ≤ ((1 - 2 / (n : ℝ)) ^ 2) ^ t :=
      pow_le_pow_left₀ hnu0 hle t
    nlinarith [h1, sq_nonneg ((n:ℝ) - 1)]
  linarith [mom2_le hn t, hpow]

end Moments


section Chain

variable {n : ℕ}

private lemma rt_transl (a b ρ : Equiv.Perm (Fin n)) :
    randomTranspositions n (a * ρ) (b * ρ) = randomTranspositions n a b := by
  rw [randomTranspositions, groupWalk, groupWalk]
  congr 1
  group

private lemma rt_pow_transl (hn : 2 ≤ n) : ∀ (t : ℕ) (a b ρ : Equiv.Perm (Fin n)),
    ((randomTranspositions n) ^ t) (a * ρ) (b * ρ) = ((randomTranspositions n) ^ t) a b := by
  intro t
  induction t with
  | zero =>
      intro a b ρ
      rw [pow_zero, Matrix.one_apply, Matrix.one_apply]
      by_cases h : a = b
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun hc => h (mul_right_cancel hc))]
  | succ t ih =>
      intro a b ρ
      have hL : ((randomTranspositions n) ^ (t + 1)) (a * ρ) (b * ρ)
          = ∑ w, ((randomTranspositions n) ^ t) (a * ρ) w * randomTranspositions n w (b * ρ) := by
        rw [pow_succ, Matrix.mul_apply]
      have hR : ((randomTranspositions n) ^ (t + 1)) a b
          = ∑ w, ((randomTranspositions n) ^ t) a w * randomTranspositions n w b := by
        rw [pow_succ, Matrix.mul_apply]
      rw [hL, hR, ← Equiv.sum_comp (Equiv.mulRight ρ)
        (fun w => ((randomTranspositions n) ^ t) (a * ρ) w * randomTranspositions n w (b * ρ))]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [Equiv.coe_mulRight]
      rw [ih a w ρ, rt_transl]

private lemma rt_pow_add_pos (hn : 2 ≤ n) {t₁ t₂ : ℕ} {a b c : Equiv.Perm (Fin n)}
    (h1 : 0 < ((randomTranspositions n) ^ t₁) a b)
    (h2 : 0 < ((randomTranspositions n) ^ t₂) b c) :
    0 < ((randomTranspositions n) ^ (t₁ + t₂)) a c := by
  rw [pow_add, Matrix.mul_apply]
  refine lt_of_lt_of_le (mul_pos h1 h2) ?_
  exact Finset.single_le_sum
    (f := fun w => ((randomTranspositions n) ^ t₁) a w * ((randomTranspositions n) ^ t₂) w c)
    (fun w _ => mul_nonneg (pow_nonneg_rt hn t₁ a w) (pow_nonneg_rt hn t₂ w c))
    (Finset.mem_univ b)

private lemma rt_swap_pos (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    0 < randomTranspositions n 1 (Equiv.swap i j) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [randomTranspositions, groupWalk, inv_one, mul_one, transpositionDist,
    if_neg (swap_ne_one hij), if_pos ⟨i, j, hij, rfl⟩]
  positivity

private lemma rt_self_pos (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    0 < randomTranspositions n σ σ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [randomTranspositions, groupWalk, mul_inv_cancel, transpositionDist, if_pos rfl]
  positivity

private lemma rt_irreducible (hn : 2 ≤ n) : Irreducible (randomTranspositions n) := by
  have key : ∀ g : Equiv.Perm (Fin n), ∃ t : ℕ, 0 < ((randomTranspositions n) ^ t) 1 g := by
    intro g
    have hmem : g ∈ Submonoid.closure {σ : Equiv.Perm (Fin n) | σ.IsSwap} := by
      rw [Equiv.Perm.mclosure_isSwap]
      exact Submonoid.mem_top g
    refine Submonoid.closure_induction ?_ ?_ ?_ hmem
    · rintro x ⟨i, j, hij, rfl⟩
      exact ⟨1, by rw [pow_one]; exact rt_swap_pos hn hij⟩
    · exact ⟨0, by rw [pow_zero, Matrix.one_apply_eq]; norm_num⟩
    · rintro a b - - ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
      refine ⟨t₂ + t₁, ?_⟩
      have h₁' : 0 < ((randomTranspositions n) ^ t₁) b (a * b) := by
        have := rt_pow_transl hn t₁ 1 a b
        rw [one_mul] at this
        rw [this]
        exact h₁
      exact rt_pow_add_pos hn h₂ h₁'
  intro x y
  obtain ⟨t, ht⟩ := key (y * x⁻¹)
  refine ⟨t, ?_⟩
  have h := rt_pow_transl hn t 1 (y * x⁻¹) x
  rw [one_mul, inv_mul_cancel_right] at h
  rw [h]
  exact ht

private lemma rt_aperiodic (hn : 2 ≤ n) : Aperiodic (randomTranspositions n) := by
  intro x
  have h1 : (1 : ℕ) ∈ returnSet (randomTranspositions n) x := by
    refine ⟨le_refl 1, ?_⟩
    rw [pow_one]
    exact rt_self_pos hn x
  have hset : {d : ℕ | ∀ t ∈ returnSet (randomTranspositions n) x, d ∣ t} = {1} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact Nat.dvd_one.mp (h 1 h1)
    · intro h t _
      rw [h]
      exact one_dvd t
  rw [period, hset, csSup_singleton]

private lemma rt_col_sum (hn : 2 ≤ n) (τ : Equiv.Perm (Fin n)) :
    ∑ σ : Equiv.Perm (Fin n), randomTranspositions n σ τ = 1 := by
  have hsum : ∑ h : Equiv.Perm (Fin n), transpositionDist n h = 1 := by
    have h0 := (rt_stochastic hn).2 (1 : Equiv.Perm (Fin n))
    rw [Finset.sum_congr rfl fun τ' (_ : τ' ∈ Finset.univ) =>
      (by rw [randomTranspositions, groupWalk, inv_one, mul_one] :
        randomTranspositions n 1 τ' = transpositionDist n τ')] at h0
    exact h0
  rw [← hsum]
  refine Fintype.sum_equiv ((Equiv.inv (Equiv.Perm (Fin n))).trans (Equiv.mulLeft τ))
    (fun σ => randomTranspositions n σ τ) (transpositionDist n) (fun σ => ?_)
  rfl

private lemma rt_stationary (hn : 2 ≤ n) :
    IsStationary (randomTranspositions n) (uniformDist (Equiv.Perm (Fin n))) := by
  have hN : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    have : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos
    exact_mod_cast this
  refine ⟨⟨fun x => by simp only [uniformDist]; positivity, ?_⟩, ?_⟩
  · simp only [uniformDist]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · ext y
    simp only [Matrix.vecMul, dotProduct, uniformDist]
    rw [← Finset.mul_sum, rt_col_sum hn, mul_one]

private lemma rt_mix_nonempty (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    {t : ℕ | distStationary (randomTranspositions n) (uniformDist (Equiv.Perm (Fin n))) t
      ≤ ε}.Nonempty := by
  obtain ⟨c, ⟨hc0, hc1⟩, C, hC, hbd⟩ := convergence_theorem (randomTranspositions n)
    (rt_stochastic hn) (rt_irreducible hn) (rt_aperiodic hn)
    (uniformDist (Equiv.Perm (Fin n))) (rt_stationary hn)
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < ε / C by positivity) hc1
  refine ⟨t, le_trans (hbd t) ?_⟩
  calc C * c ^ t ≤ C * (ε / C) := mul_le_mul_of_nonneg_left ht.le hC.le
    _ = ε := by field_simp


end Chain


section Final

variable {n : ℕ}

private lemma sum_ggf (hn : 2 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n), ggf σ = 0 := by
  have h1 : ∑ σ : Equiv.Perm (Fin n), fpR σ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    simp only [fpR]
    push_cast [← Nat.cast_sum]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (sum_fixN (by omega : 0 < n))
  simp only [ggf]
  rw [Finset.sum_sub_distrib, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

private lemma sum_ggf_sq (hn : 2 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n), (ggf σ) ^ 2 = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  have h1 : ∑ σ : Equiv.Perm (Fin n), fpR σ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    simp only [fpR]
    push_cast [← Nat.cast_sum]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (sum_fixN (by omega : 0 < n))
  have h2 : ∑ σ : Equiv.Perm (Fin n), (fpR σ) ^ 2
      = 2 * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    have := sum_fixN_sq hn
    have hc := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at hc
    simp only [fpR]
    exact_mod_cast hc
  have hexp : ∀ σ : Equiv.Perm (Fin n), (ggf σ) ^ 2 = (fpR σ) ^ 2 - 2 * fpR σ + 1 := by
    intro σ
    rw [ggf]
    ring
  rw [Finset.sum_congr rfl fun σ _ => hexp σ, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    h2, ← Finset.mul_sum, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

private lemma distExp_unif (hn : 2 ≤ n) :
    distExp (uniformDist (Equiv.Perm (Fin n))) ggf = 0 := by
  rw [distExp]
  simp only [uniformDist]
  rw [← Finset.sum_mul, sum_ggf hn, zero_mul]

private lemma distVar_unif (hn : 2 ≤ n) :
    distVar (uniformDist (Equiv.Perm (Fin n))) ggf = 1 := by
  have hN : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    have : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos
    exact_mod_cast this
  rw [distVar, distExp_unif hn]
  simp only [uniformDist, sub_zero]
  rw [← Finset.sum_mul, sum_ggf_sq hn]
  field_simp

private lemma distExp_row (hn : 2 ≤ n) (t : ℕ) :
    distExp (rowDist (randomTranspositions n) t (1 : Equiv.Perm (Fin n))) ggf = mom1 n t := by
  rw [distExp, mom1]
  exact Finset.sum_congr rfl fun τ _ => by rw [rowDist]; ring

private lemma distVar_row (hn : 2 ≤ n) (t : ℕ) :
    distVar (rowDist (randomTranspositions n) t (1 : Equiv.Perm (Fin n))) ggf
      = mom2 n t - (mom1 n t) ^ 2 := by
  rw [distVar, distExp_row hn]
  have hexp : ∀ τ : Equiv.Perm (Fin n),
      (ggf τ - mom1 n t) ^ 2 * rowDist (randomTranspositions n) t 1 τ
        = ((randomTranspositions n) ^ t) 1 τ * (ggf τ) ^ 2
          - 2 * mom1 n t * (((randomTranspositions n) ^ t) 1 τ * ggf τ)
          + (mom1 n t) ^ 2 * ((randomTranspositions n) ^ t) 1 τ := by
    intro τ
    rw [rowDist]
    ring
  rw [Finset.sum_congr rfl fun τ _ => hexp τ, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← mom1, ← mom2, pow_sum_rt hn t 1, mul_one]
  ring

private lemma distVar_nonneg {V : Type*} [Fintype V] [DecidableEq V] (μ : V → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (f : V → ℝ) : 0 ≤ distVar μ f := by
  refine Finset.sum_nonneg fun x _ => ?_
  exact mul_nonneg (sq_nonneg _) (hμ x)

private lemma log_one_sub_ge {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    -(u / (1 - u)) ≤ Real.log (1 - u) := by
  have h1 : (0 : ℝ) < 1 - u := by linarith
  have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (1 - u) by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt h1), Real.log_one, zero_sub] at h2
  have h3 : 1 / (1 - u) - 1 = u / (1 - u) := by field_simp; ring
  rw [h3] at h2
  linarith

private lemma log_le_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * (Real.sqrt x - 1) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← Real.mul_self_sqrt hx.le]
    rw [Real.log_mul (ne_of_gt hs) (ne_of_gt hs)]
    ring
  linarith

end Final


end

end MarkovMixing

open MarkovMixing

set_option maxHeartbeats 2000000 in
/-- **Proposition 8.11** (LPW): for the random transpositions chain on `n`
cards and `0 < ε < 1`, `t_mix(ε) ≥ ((n−1)/2) log((1−ε)n/6)`. -/
theorem solution (n : ℕ) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((n : ℝ) - 1) / 2 * Real.log ((1 - ε) * n / 6) ≤
      (mixingTime (randomTranspositions n)
        (uniformDist (Equiv.Perm (Fin n))) ε : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hβ0 : (0 : ℝ) < 1 - ε := by linarith
  have hApos : (0 : ℝ) < (1 - ε) * (n : ℝ) / 6 := by positivity
  by_cases hA1 : (1 - ε) * (n : ℝ) / 6 ≤ 1
  · have hlog : Real.log ((1 - ε) * (n : ℝ) / 6) ≤ 0 := Real.log_nonpos hApos.le hA1
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hle : ((n : ℝ) - 1) / 2 * Real.log ((1 - ε) * (n : ℝ) / 6) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog
    exact le_trans hle (Nat.cast_nonneg _)
  push_neg at hA1
  -- the non-trivial regime
  have hnbig : 7 ≤ n := by
    by_contra hc
    push_neg at hc
    have h1 : (n : ℝ) ≤ 6 := by
      have : n ≤ 6 := by omega
      exact_mod_cast this
    nlinarith
  have hn7 : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnbig
  set A : ℝ := (1 - ε) * (n : ℝ) / 6 with hA
  set L : ℝ := Real.log A with hL
  have hL0 : 0 < L := Real.log_pos hA1
  set T : ℕ := mixingTime (randomTranspositions n) (uniformDist (Equiv.Perm (Fin n))) ε with hT
  have hmem : distStationary (randomTranspositions n)
      (uniformDist (Equiv.Perm (Fin n))) T ≤ ε := by
    have := Nat.sInf_mem (rt_mix_nonempty hn ε hε)
    simpa [hT, mixingTime] using this
  by_contra hcon
  push_neg at hcon
  -- the mean at time T
  have hlam0 : (0 : ℝ) < 1 - 2 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hnR]
    linarith
  have hm : mom1 n T = ((n : ℝ) - 1) * (1 - 2 / (n : ℝ)) ^ T := mom1_eq hn T
  have hlogl : -(2 / ((n : ℝ) - 2)) ≤ Real.log (1 - 2 / (n : ℝ)) := by
    have h := log_one_sub_ge (show (0:ℝ) < 2 / (n:ℝ) by positivity)
      (by rw [div_lt_one hnR]; linarith)
    have he : (2 / (n : ℝ)) / (1 - 2 / (n : ℝ)) = 2 / ((n : ℝ) - 2) := by
      field_simp
      try ring
    rwa [he] at h
  have hpowT : ((n : ℝ) - 1) * Real.exp (-(((n : ℝ) - 1) * L / ((n : ℝ) - 2)))
      ≤ mom1 n T := by
    rw [hm]
    have hpe : (1 - 2 / (n : ℝ)) ^ T = Real.exp ((T : ℝ) * Real.log (1 - 2 / (n : ℝ))) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [hpe]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
    have hTle : (T : ℝ) ≤ ((n : ℝ) - 1) / 2 * L := le_of_lt hcon
    have hd : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    have h1 : (T : ℝ) * (-(2 / ((n : ℝ) - 2))) ≤ (T : ℝ) * Real.log (1 - 2 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogl (Nat.cast_nonneg T)
    have hTle' : (T : ℝ) * 2 ≤ ((n : ℝ) - 1) * L := by
      have he2 : ((n : ℝ) - 1) / 2 * L = ((n : ℝ) - 1) * L / 2 := by ring
      rw [he2] at hTle
      linarith
    have hinv : (0 : ℝ) < 1 / ((n : ℝ) - 2) := by positivity
    have h2 : -(((n : ℝ) - 1) * L / ((n : ℝ) - 2)) ≤ (T : ℝ) * (-(2 / ((n : ℝ) - 2))) := by
      have hmul := mul_le_mul_of_nonneg_right hTle' hinv.le
      have e1 : (T : ℝ) * (-(2 / ((n : ℝ) - 2))) = -((T : ℝ) * 2 * (1 / ((n : ℝ) - 2))) := by
        field_simp
      have e2 : ((n : ℝ) - 1) * L / ((n : ℝ) - 2) = ((n : ℝ) - 1) * L * (1 / ((n : ℝ) - 2)) := by
        field_simp
      rw [e1, e2]
      linarith
    linarith
  -- lower bound on (1 - ε) * mom1
  have hkey : (4 : ℝ) ≤ (1 - ε) * mom1 n T := by
    have hd : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    have hsplit : Real.exp (-(((n : ℝ) - 1) * L / ((n : ℝ) - 2)))
        = Real.exp (-L) * Real.exp (-(L / ((n : ℝ) - 2))) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have hexpL : Real.exp (-L) = 1 / A := by
      rw [hL, Real.exp_neg, Real.exp_log hApos]
      ring
    have hs : Real.sqrt ((n : ℝ) / 6) ^ 2 = (n : ℝ) / 6 :=
      Real.sq_sqrt (by positivity)
    have hs0 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) / 6) := Real.sqrt_nonneg _
    have hLle : L ≤ 2 * (Real.sqrt ((n : ℝ) / 6) - 1) := by
      refine le_trans (log_le_sqrt hApos) ?_
      have hAle : A ≤ (n : ℝ) / 6 := by
        rw [hA]
        have : (1 - ε) * (n : ℝ) ≤ (n : ℝ) := by nlinarith
        linarith
      have := Real.sqrt_le_sqrt hAle
      linarith
    have hratio : L / ((n : ℝ) - 2) ≤ 2 / 9 := by
      rw [div_le_div_iff₀ hd (by norm_num)]
      have hq : 12 * Real.sqrt ((n : ℝ) / 6) ^ 2 - 18 * Real.sqrt ((n : ℝ) / 6) + 14 ≥ 0 := by
        nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) / 6) - 3 / 4)]
      rw [hs] at hq
      nlinarith [hLle, hd]
    have hexp2 : (1 : ℝ) - L / ((n : ℝ) - 2) ≤ Real.exp (-(L / ((n : ℝ) - 2))) := by
      have := Real.add_one_le_exp (-(L / ((n : ℝ) - 2)))
      linarith
    have hchain : (1 - ε) * (((n : ℝ) - 1)
        * Real.exp (-(((n : ℝ) - 1) * L / ((n : ℝ) - 2)))) ≥ 4 := by
      rw [hsplit, hexpL]
      have hpos1 : (0 : ℝ) ≤ (1 - ε) * ((n : ℝ) - 1) := by nlinarith
      have hid : (1 - ε) * (((n : ℝ) - 1) * (1 / A * Real.exp (-(L / ((n : ℝ) - 2)))))
          = 6 * (((n : ℝ) - 1) / (n : ℝ)) * Real.exp (-(L / ((n : ℝ) - 2))) := by
        rw [hA]
        field_simp
        try ring
      rw [hid]
      have h79 : (7 : ℝ) / 9 ≤ Real.exp (-(L / ((n : ℝ) - 2))) := by linarith
      have h67 : (6 : ℝ) / 7 ≤ ((n : ℝ) - 1) / (n : ℝ) := by
        rw [div_le_div_iff₀ (by norm_num) hnR]
        linarith
      nlinarith [h79, h67, Real.exp_pos (-(L / ((n : ℝ) - 2)))]
    have hmono : (1 - ε) * (((n : ℝ) - 1)
        * Real.exp (-(((n : ℝ) - 1) * L / ((n : ℝ) - 2)))) ≤ (1 - ε) * mom1 n T :=
      mul_le_mul_of_nonneg_left hpowT hβ0.le
    linarith
  -- the distinguishing statistic
  have hm0 : (0 : ℝ) < mom1 n T := by nlinarith [hkey, hβ0]
  have hvar := var_le (show 4 ≤ n by omega) T
  have hv0 : (0 : ℝ) ≤ mom2 n T - (mom1 n T) ^ 2 := by
    rw [← distVar_row hn T]
    exact distVar_nonneg _ (fun x => by rw [rowDist]; exact pow_nonneg_rt hn T 1 x) ggf
  set v : ℝ := mom2 n T - (mom1 n T) ^ 2 with hvdef
  have hc1 : (2 * (n : ℝ) - 4) / (2 * (n : ℝ) - 2) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hc2 : (6 * (n : ℝ) - 6) / (4 * (n : ℝ) - 2) ≤ 3 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hvle : v ≤ mom1 n T + 3 / 2 := by
    have h1 : (2 * (n : ℝ) - 4) / (2 * (n : ℝ) - 2) * mom1 n T ≤ mom1 n T :=
      mul_le_of_le_one_left hm0.le hc1
    linarith [hvar]
  -- apply the distinguishing statistic
  set w : ℝ := (v + 1) / 2 with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  set r : ℝ := mom1 n T / Real.sqrt w with hr
  have hsq : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw0.le
  have hsqrt0 : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw0
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hdist1 : IsDist (rowDist (randomTranspositions n) T (1 : Equiv.Perm (Fin n))) := by
    refine ⟨fun x => by rw [rowDist]; exact pow_nonneg_rt hn T 1 x, ?_⟩
    rw [Finset.sum_congr rfl fun y _ => (by rw [rowDist] :
      rowDist (randomTranspositions n) T 1 y = ((randomTranspositions n) ^ T) 1 y)]
    exact pow_sum_rt hn T 1
  have hdist2 : IsDist (uniformDist (Equiv.Perm (Fin n))) := (rt_stationary hn).1
  have hvarsum : distVar (rowDist (randomTranspositions n) T 1) ggf
      + distVar (uniformDist (Equiv.Perm (Fin n))) ggf = v + 1 := by
    rw [distVar_row hn T, distVar_unif hn, ← hvdef]
  have hmeans : distExp (rowDist (randomTranspositions n) T 1) ggf
      - distExp (uniformDist (Equiv.Perm (Fin n))) ggf = mom1 n T := by
    rw [distExp_row hn T, distExp_unif hn, sub_zero]
  have hne : distExp (rowDist (randomTranspositions n) T 1) ggf
      ≠ distExp (uniformDist (Equiv.Perm (Fin n))) ggf := by
    intro hc
    rw [hc, sub_self] at hmeans
    linarith [hm0, hmeans]
  have hhyp : r * Real.sqrt ((distVar (rowDist (randomTranspositions n) T 1) ggf
      + distVar (uniformDist (Equiv.Perm (Fin n))) ggf) / 2)
      ≤ |distExp (rowDist (randomTranspositions n) T 1) ggf
        - distExp (uniformDist (Equiv.Perm (Fin n))) ggf| := by
    rw [hvarsum, ← hw, hmeans, abs_of_pos hm0, hr, div_mul_cancel₀ _ (ne_of_gt hsqrt0)]
  have hds := distinguishing_statistic_nondegenerate
    (rowDist (randomTranspositions n) T 1) (uniformDist (Equiv.Perm (Fin n)))
    hdist1 hdist2 ggf hne r hr0 hhyp
  have htv : tvDist (rowDist (randomTranspositions n) T 1)
      (uniformDist (Equiv.Perm (Fin n))) ≤ ε := by
    refine le_trans ?_ hmem
    rw [distStationary]
    exact le_ciSup (Set.Finite.bddAbove
      (Set.range fun z : Equiv.Perm (Fin n) =>
        tvDist (rowDist (randomTranspositions n) T z)
          (uniformDist (Equiv.Perm (Fin n)))).toFinite) (1 : Equiv.Perm (Fin n))
  have hrsq : r ^ 2 = (mom1 n T) ^ 2 / w := by
    rw [hr, div_pow, hsq]
  have hfin : (1 - ε) * (2 * (mom1 n T) ^ 2) ≤ 4 * ε * (v + 1) := by
    have h4 : (0 : ℝ) < 4 + r ^ 2 := by positivity
    have h1 : 1 - 4 / (4 + r ^ 2) ≤ ε := le_trans hds htv
    have h2 : (1 - ε) * (4 + r ^ 2) ≤ 4 := by
      rw [← sub_nonneg] at h1
      have := mul_le_mul_of_nonneg_right (by linarith : 1 - ε ≤ 4 / (4 + r ^ 2)) h4.le
      rw [div_mul_cancel₀ _ (ne_of_gt h4)] at this
      exact this
    have hv1 : (0 : ℝ) < v + 1 := by linarith
    have he : (mom1 n T) ^ 2 / ((v + 1) / 2) = 2 * (mom1 n T) ^ 2 / (v + 1) := by
      field_simp
      try ring
    rw [hrsq, hw, he] at h2
    have h3 : (1 - ε) * (2 * (mom1 n T) ^ 2 / (v + 1)) ≤ 4 * ε := by linarith
    rw [mul_div_assoc', div_le_iff₀ hv1] at h3
    linarith
  -- contradiction
  have hb1 : (1 - ε) * (2 * (mom1 n T) ^ 2) ≥ 8 * mom1 n T := by
    nlinarith [hkey, hm0]
  have hb2 : 4 * ε * (v + 1) ≤ 4 * mom1 n T + 10 := by
    nlinarith [hvle, hε1, hε, hm0, hv0]
  have hmge : (4 : ℝ) ≤ mom1 n T := by nlinarith [hkey, hβ0, hε1, hm0]
  linarith [hfin, hb1, hb2, hmge]
