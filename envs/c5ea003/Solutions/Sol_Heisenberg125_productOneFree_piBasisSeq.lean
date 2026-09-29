-- Prove2me | solution 1 for Heisenberg125.productOneFree_piBasisSeq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T20:32:53.192462+00:00
-- url     : https://prove2.me/submissions/aecec741-68fd-475f-8c4e-a8e09a2314ab

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_ElementaryAbelian

open Heisenberg125 in
theorem solution {p k : ℕ} (hp : 1 < p) : ProductOneFree (piBasisSeq p k) := by
  classical
  haveI : NeZero p := ⟨by omega⟩
  have hone : (1 : ZMod p) ≠ 0 := by
    haveI : Fact (1 < p) := ⟨hp⟩
    exact one_ne_zero
  have hinj : ∀ i j : Fin k, piBasis p k j = piBasis p k i ↔ j = i := by
    intro i j
    constructor
    · intro h
      by_contra hne
      have h1 := congrFun (congrArg Multiplicative.toAdd h) j
      simp [piBasis, Pi.single_apply, hne] at h1
      exact hone h1
    · rintro rfl
      rfl
  have hsmall : ∀ n : ℕ, n < p → (n : ZMod p) = 0 → n = 0 := by
    intro n hn h
    exact Nat.eq_zero_of_dvd_of_lt ((CharP.cast_eq_zero_iff (ZMod p) p n).1 h) hn
  -- each coordinate of a product of basis vectors counts that basis vector
  have hcoord : ∀ M : List (Multiplicative (Fin k → ZMod p)),
      (∀ g ∈ M, ∃ j, g = piBasis p k j) →
      ∀ i, Multiplicative.toAdd M.prod i = (M.count (piBasis p k i) : ZMod p) := by
    intro M hM i
    induction M with
    | nil => simp
    | cons g M ih =>
      obtain ⟨j, rfl⟩ := hM g List.mem_cons_self
      have ih' := ih (fun g hg => hM g (List.mem_cons_of_mem _ hg))
      rw [List.prod_cons, toAdd_mul, Pi.add_apply, ih', List.count_cons]
      by_cases hji : j = i
      · subst hji
        simp [piBasis]
        ring
      · have hne : ¬ (piBasis p k j == piBasis p k i) = true := by
          simp only [beq_iff_eq]
          exact fun h => hji ((hinj i j).1 h)
        simp only [hne, if_false, Nat.cast_add, Nat.cast_zero, add_zero]
        simp [piBasis, Pi.single_apply, Ne.symm hji]
  have hcountL : ∀ i, (piBasisSeq p k).count (piBasis p k i) = p - 1 := by
    intro i
    unfold piBasisSeq
    rw [List.count_flatMap]
    have e : (List.finRange k).map (fun j => (List.replicate (p - 1) (piBasis p k j)).count
        (piBasis p k i)) = (List.finRange k).map (fun j => if j = i then p - 1 else 0) := by
      refine List.map_congr_left (fun j _ => ?_)
      rw [List.count_replicate]
      by_cases hji : j = i
      · subst hji
        simp
      · have : ¬ (piBasis p k j == piBasis p k i) = true := by
          simp only [beq_iff_eq]
          exact fun h => hji ((hinj i j).1 h)
        simp [this, hji]
    simp only [Function.comp_def] at e ⊢
    rw [e, ← Fin.sum_univ_def]
    simp
  have hmemL : ∀ g ∈ piBasisSeq p k, ∃ j, g = piBasis p k j := by
    intro g hg
    unfold piBasisSeq at hg
    rw [List.mem_flatMap] at hg
    obtain ⟨j, -, hj⟩ := hg
    exact ⟨j, List.eq_of_mem_replicate hj⟩
  intro T hT hne ⟨M, hM, hprod⟩
  have hTmem : ∀ g ∈ T, ∃ j, g = piBasis p k j := fun g hg => hmemL g (hT.subset hg)
  have hMmem : ∀ g ∈ M, ∃ j, g = piBasis p k j := fun g hg => hTmem g (hM.mem_iff.1 hg)
  have hzero : ∀ i, T.count (piBasis p k i) = 0 := by
    intro i
    have h1 := hcoord M hMmem i
    rw [hprod, toAdd_one, Pi.zero_apply, hM.count_eq] at h1
    have hle : T.count (piBasis p k i) ≤ p - 1 := by
      rw [← hcountL i]
      exact hT.count_le _
    exact hsmall _ (by omega) h1.symm
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil T hne
  obtain ⟨j, rfl⟩ := hTmem g hg
  have := hzero j
  rw [List.count_eq_zero] at this
  exact this hg
