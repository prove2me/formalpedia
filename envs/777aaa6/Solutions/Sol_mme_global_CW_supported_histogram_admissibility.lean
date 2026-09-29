-- Prove2me | solution 1 for mme_global_CW_supported_histogram_admissibility
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T10:25:15.4067+00:00
-- url     : https://prove2.me/submissions/506065bb-5ba3-4037-ad40-000e9b00b132

import Definitions.Def_mme_global_CW_histogram_frame
import Mathlib
open BigOperators MME MME.RecursiveYZ MME.GlobalCW MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem cell_fiber {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (a : RecursiveXHash.Address degree R bounds n) (r : Fin R)
    (c : RecursiveThinSplit.Split degree (bounds r)) :
    Fintype.card {p : Place n // cell a p = ⟨r,c⟩} = RecursiveThinSplit.count (a r) c := by
  classical
  let e : {p : Place n // cell a p = ⟨r,c⟩} ≃ {t : Fin (n r) // a r t = c} := {
    toFun := by
      rintro ⟨⟨r',t⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨t, eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun t ↦ ⟨⟨r,t.val⟩, by change (⟨r,_⟩ : Cell degree R bounds) = ⟨r,c⟩; rw [t.property]⟩
    left_inv := by
      rintro ⟨⟨r',t⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro t; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  rfl

private theorem histogram_mass {P C W : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (f : P → W) (c : C) :
    ∑ w, count cell f c w = Fintype.card {p : P // cell p = c} := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : cell p = c <;> simp [hp]

private theorem histogram_reflection {P C : Type*} [Fintype P] {ell : ℕ}
    (cell : P → C) (f g : P → CompleteWord ell) (c : C)
    (h : ∀ p, cell p = c → f p = fun r ↦ Fin.rev (g p r))
    (w : CompleteWord ell) : count cell f c w = count cell g c (fun r ↦ Fin.rev (w r)) := by
  classical
  unfold count
  congr 1
  ext p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hp,hw⟩
    refine ⟨hp,?_⟩
    funext r
    have hh := congrFun ((h p hp).symm.trans hw) r
    simpa using congrArg Fin.rev hh
  · rintro ⟨hp,hw⟩
    refine ⟨hp,?_⟩
    rw [h p hp,hw]
    simp

theorem solution {ell M : ℕ} (D : HistogramFrame ell M)
    (x : Fin 3 → Place D.n → CompleteWord ell)
    (hgrade : ∀ i, Graded i D.reference (x i))
    (hsupport : ∀ p r, (x 0 p r).val + (x 1 p r).val + (x 2 p r).val = 2) :
    D.Admissible (fun i ↦ count (cell D.reference) (x i)) := by
  classical
  have hjoint : ∀ r c, RecursiveThinSplit.count (D.reference r) c = D.m r c :=
    (Finset.mem_filter.mp D.reference_target).2
  have hzero (i : Fin 3) (c : Cell D.degree D.R D.bounds)
      (hc : (c.2.val i).val = 0) (p : Place D.n)
      (hp : cell D.reference p = c) (r : Fin (2^(ell-1))) :
      (x i p r).val = 0 := by
    have hh := hgrade i p
    rw [hp,hc] at hh
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)).mp hh r (Finset.mem_univ r)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i c
    rcases c with ⟨r,c⟩
    rw [histogram_mass]
    have hf := cell_fiber D.reference r c
    rw [hjoint] at hf
    simpa only [Fintype.card_eq_nat_card] using hf
  · intro i c w hw
    have hw' : ∃ p, cell D.reference p = c ∧ x i p = w := by
      simpa only [count,Finset.card_pos,Finset.Nonempty,Finset.mem_filter,Finset.mem_univ,
        true_and] using hw
    obtain ⟨p,hp,hw⟩ := hw' 
    have hg := hgrade i p
    rw [hp,hw] at hg
    exact hg
  · intro c hc w
    apply histogram_reflection
    intro p hp
    funext r
    apply Fin.ext
    have hz := hzero 2 c hc p hp r
    have hs := hsupport p r
    simp only [Fin.rev,Fin.val_mk]
    omega
  · intro c hc w
    apply histogram_reflection
    intro p hp
    funext r
    apply Fin.ext
    have hz := hzero 0 c hc p hp r
    have hs := hsupport p r
    simp only [Fin.rev,Fin.val_mk]
    omega
  · intro c hc w
    apply histogram_reflection
    intro p hp
    funext r
    apply Fin.ext
    have hz := hzero 1 c hc p hp r
    have hs := hsupport p r
    simp only [Fin.rev,Fin.val_mk]
    omega
