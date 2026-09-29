-- Prove2me | solution 1 for mme_recursive_region_derived_parent_hole_budget
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:28:57.211108+00:00
-- url     : https://prove2.me/submissions/4853ce48-1300-4b74-a98d-c8401cf95874

import Theorems.Thm_mme_recursive_region_parent_profile_concentration
import Definitions.Def_mme_recursive_yz_hash_filter

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem solution {half R ell : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (i : Fin 3) (hsupport : ∀ c w, 0 < mu c w → ∑ h, (w h).val = (c.2.val i).val)
    (k d : ℕ) (hk : 0 < k) (hkn : ∀ r, k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) ≤
      (k : ℝ) * eps ^ 2)
    (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m) :
    8 * d * (typeHoles htotal i a mu (parentTypical htotal n m mu eps)).card ≤
      (unbrokenWords htotal i a mu).card := by
  classical
  have hgraded (f : Position n → CompleteSplit.CompleteWord ell)
      (hf : Useful (fullCell htotal a) mu f) : Graded htotal i a f := by
    intro p
    have hp : 0 < mu (fullCell htotal a p) (f p) := by
      rw [← hf]
      unfold count
      apply Finset.card_pos.mpr
      refine ⟨p, ?_⟩
      simp
    exact hsupport _ _ hp
  let U := {f : Position n → CompleteSplit.CompleteWord ell // Useful (fullCell htotal a) mu f}
  let H := {f : U // ¬ parentTypical htotal n m mu eps f.val}
  have hu : Fintype.card U = (unbrokenWords htotal i a mu).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext f
    simp only [unbrokenWords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hf ↦ ⟨hgraded f hf,hf⟩,fun hf ↦ hf.2⟩
  have hh : Fintype.card H = (typeHoles htotal i a mu (parentTypical htotal n m mu eps)).card := by
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun f ↦ Useful (fullCell htotal a) mu f) (fun f ↦ ¬ parentTypical htotal n m mu eps f)),
      Fintype.card_subtype]
    congr 1
    ext f
    simp only [typeHoles, unbrokenWords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ ⟨⟨hgraded f h.1,h.1⟩,h.2⟩,fun h ↦ ⟨h.1.2,h.2⟩⟩
  rw [← hh, ← hu]
  by_cases hd : d = 0
  · simp [hd]
  have hd' : (0 : ℝ) < 8 * d := by positivity
  by_cases hU : Fintype.card U = 0
  · have hH : Fintype.card H = 0 := Nat.eq_zero_of_le_zero (hU ▸ Fintype.card_subtype_le _)
    simp [hH]
  have hU' : (0 : ℝ) < Fintype.card U := by exact_mod_cast (Nat.pos_of_ne_zero hU)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : (0 : ℝ) < (k : ℝ) * eps ^ 2 := by positivity
  have hprob := mme_recursive_region_parent_profile_concentration parent n htotal m mu hmass
    k hk hkn hdiv eps heps a ha
  have hmean : (𝔼 f : U, if ¬ parentTypical htotal n m mu eps f.val then (1 : ℝ) else 0) =
      (Fintype.card H : ℝ) / Fintype.card U := by
    rw [Fintype.expect_eq_sum_div_card]
    congr 1
    change (∑ f : {f : Position n → CompleteSplit.CompleteWord ell // Useful (fullCell htotal a) mu f},
      if ¬ parentTypical htotal n m mu eps f.val then (1 : ℝ) else 0) = (Fintype.card H : ℝ)
    simp only [H, U, Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hmean] at hprob
  have hsmall : 25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2 /
      ((k : ℝ) * eps ^ 2) ≤ 1 / (8 * d) := by
    apply (div_le_div_iff₀ hden hd').mpr
    simpa only [one_mul, mul_one, mul_comm] using hscale
  have h := (div_le_div_iff₀ hU' hd').mp (hprob.trans hsmall)
  have hf : (8 : ℝ) * d * Fintype.card H ≤ Fintype.card U := by nlinarith
  exact_mod_cast hf
