-- Prove2me | solution 2 for ShorIrreducible.fidelity_shorState_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:51:45.946783+00:00
-- url     : https://prove2.me/submissions/e940aae3-785b-4fb9-a276-b1c80394e81a

import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorTruncationBound

set_option maxHeartbeats 4000000 in
open Finset Matrix IITTensorNetwork ShorIrreducible in
theorem solution {β : Type*} [Fintype β] [DecidableEq β]
    {r m : ℕ} {F : Fin (r * m) → β} (hr : 0 < r) (hm : 0 < m)
    (hF : HasExactPeriod r F) {δ : Type*} [Fintype δ] [DecidableEq δ]
    {A : Matrix (Fin (r * m)) β ℂ} {P : Matrix (Fin (r * m)) δ ℂ} {Q : Matrix β δ ℂ}
    {s : δ → ℝ} (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1)
    (hA : A = P * Matrix.diagonal (fun k => (s k : ℂ)) * Qᴴ) (hs : ∑ k, s k ^ 2 ≤ 1) :
    ‖frobInner (shorState (r * m) F) A‖ ^ 2 ≤ (Fintype.card δ : ℝ) / (r : ℝ) := by
  classical
  ---- 0.  numerics for the flat amplitude
  have hrm : 0 < r * m := Nat.mul_pos hr hm
  have hrmR : (0:ℝ) < ((r * m : ℕ) : ℝ) := by exact_mod_cast hrm
  have hr0 : (0:ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hm0 : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, (Real.sqrt ((r * m : ℕ) : ℝ))⁻¹ = c := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [← hcdef]; positivity
  have hc2 : c ^ 2 = (((r * m : ℕ) : ℝ))⁻¹ := by
    rw [← hcdef, inv_pow, Real.sq_sqrt hrmR.le]
  ---- 1.  conj z * z as a real square
  have hkey : ∀ z : ℂ, star z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    intro z
    rw [← starRingEnd_apply]
    exact RCLike.conj_mul z
  have hstarR : ∀ x : ℝ, star ((x : ℂ)) = ((x : ℂ)) := by
    intro x
    rw [← starRingEnd_apply, Complex.conj_ofReal]
  ---- 2.  the columns of an isometry are unit vectors
  have hPcol : ∀ k : δ, ∑ f : Fin (r * m), ‖P f k‖ ^ 2 = 1 := by
    intro k
    have h := congrFun (congrFun hP k) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have h2 : ((∑ f : Fin (r * m), ‖P f k‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun f _ => by rw [Complex.ofReal_pow, ← hkey])
    exact_mod_cast h2
  have hQcol : ∀ k : δ, ∑ g : β, ‖Q g k‖ ^ 2 = 1 := by
    intro k
    have h := congrFun (congrFun hQ k) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have h2 : ((∑ g : β, ‖Q g k‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun g _ => by rw [Complex.ofReal_pow, ← hkey])
    exact_mod_cast h2
  ---- 3.  each residue class mod r inside Fin (r * m) has exactly m elements
  have hcount : ∀ c₀ : ℕ, c₀ < r →
      (univ.filter (fun y : Fin (r * m) => (y : ℕ) % r = c₀)).card = m := by
    intro c₀ hc₀
    have hlt : ∀ q : Fin m, c₀ + r * (q : ℕ) < r * m := by
      intro q
      have hq : (q : ℕ) + 1 ≤ m := q.2
      calc c₀ + r * (q : ℕ) < r + r * (q : ℕ) := by omega
        _ = r * ((q : ℕ) + 1) := by ring
        _ ≤ r * m := Nat.mul_le_mul_left r hq
    set e : Fin m → Fin (r * m) := fun q => ⟨c₀ + r * (q : ℕ), hlt q⟩ with he
    have hinj : Function.Injective e := by
      intro a b hab
      have h1 : c₀ + r * (a : ℕ) = c₀ + r * (b : ℕ) := congrArg Fin.val hab
      have h2 : r * (a : ℕ) = r * (b : ℕ) := by omega
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left hr h2)
    have himg : (univ : Finset (Fin m)).image e
        = univ.filter (fun y : Fin (r * m) => (y : ℕ) % r = c₀) := by
      ext y
      simp only [mem_image, mem_univ, true_and, mem_filter]
      constructor
      · rintro ⟨q, rfl⟩
        simp only [he]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc₀]
      · intro hy
        refine ⟨⟨(y : ℕ) / r, ?_⟩, ?_⟩
        · have hylt : (y : ℕ) < r * m := y.2
          have hcomm : r * m = m * r := Nat.mul_comm r m
          rw [Nat.div_lt_iff_lt_mul hr]
          omega
        · refine Fin.ext ?_
          simp only [he]
          have hdm := Nat.div_add_mod (y : ℕ) r
          omega
    rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  ---- 4.  every fibre of F has at most m elements
  have hfib : ∀ g : β, (univ.filter (fun f : Fin (r * m) => F f = g)).card ≤ m := by
    intro g
    by_cases hg : ∃ x : Fin (r * m), F x = g
    · obtain ⟨x, rfl⟩ := hg
      have hset : (univ.filter (fun f : Fin (r * m) => F f = F x))
          = univ.filter (fun f : Fin (r * m) => (f : ℕ) % r = (x : ℕ) % r) := by
        ext f
        simp only [mem_filter, mem_univ, true_and]
        exact hF f x
      rw [hset, hcount ((x : ℕ) % r) (Nat.mod_lt _ hr)]
    · push_neg at hg
      have hempty : (univ.filter (fun f : Fin (r * m) => F f = g)) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun f _ => hg f)
      rw [hempty]
      simp
  ---- 5.  pulling a unit vector back along F costs at most a factor m
  have hQF : ∀ k : δ, ∑ f : Fin (r * m), ‖Q (F f) k‖ ^ 2 ≤ (m : ℝ) := by
    intro k
    have hfw := Finset.sum_fiberwise_of_maps_to
      (s := (univ : Finset (Fin (r * m)))) (t := (univ : Finset β)) (g := F)
      (fun f _ => mem_univ _) (fun f => ‖Q (F f) k‖ ^ 2)
    rw [← hfw]
    have hconst : ∀ g ∈ (univ : Finset β),
        (∑ f ∈ univ.filter (fun f : Fin (r * m) => F f = g), ‖Q (F f) k‖ ^ 2)
          = ((univ.filter (fun f : Fin (r * m) => F f = g)).card : ℝ) * ‖Q g k‖ ^ 2 := by
      intro g _
      rw [Finset.sum_congr rfl (fun f hf => by rw [(Finset.mem_filter.mp hf).2]),
        Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hconst]
    have hle : ∀ g ∈ (univ : Finset β),
        ((univ.filter (fun f : Fin (r * m) => F f = g)).card : ℝ) * ‖Q g k‖ ^ 2
          ≤ (m : ℝ) * ‖Q g k‖ ^ 2 := by
      intro g _
      have h1 : ((univ.filter (fun f : Fin (r * m) => F f = g)).card : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hfib g
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    refine le_trans (Finset.sum_le_sum hle) ?_
    rw [← Finset.mul_sum, hQcol k, mul_one]
  ---- 6.  the diagonal of Qᴴ Mᴴ P is bounded by 1/√r
  have hNkk : ∀ k : δ, ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖ ^ 2 ≤ 1 / (r : ℝ) := by
    intro k
    have hform : (Qᴴ * (shorState (r * m) F)ᴴ * P) k k
        = ∑ f : Fin (r * m), (star (Q (F f) k) * (c : ℂ)) * P f k := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun f _ => ?_)
      congr 1
      rw [Matrix.mul_apply]
      have hterm : ∀ g : β, (Qᴴ) k g * ((shorState (r * m) F)ᴴ) g f
          = if F f = g then star (Q g k) * (c : ℂ) else 0 := by
        intro g
        simp only [Matrix.conjTranspose_apply]
        have hM : shorState (r * m) F f g
            = if F f = g then (((Real.sqrt ((r * m : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) else 0 := rfl
        rw [hM, hcdef]
        by_cases hg : F f = g
        · rw [if_pos hg, if_pos hg, hstarR]
        · rw [if_neg hg, if_neg hg, star_zero, mul_zero]
      rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_ite_eq]
      simp
    have hb : ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖
        ≤ ∑ f : Fin (r * m), (c * ‖Q (F f) k‖) * ‖P f k‖ := by
      rw [hform]
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun f _ => ?_)
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
      ring
    have hb2 : (∑ f : Fin (r * m), (c * ‖Q (F f) k‖) * ‖P f k‖) ^ 2
        ≤ (∑ f : Fin (r * m), (c * ‖Q (F f) k‖) ^ 2) * (∑ f : Fin (r * m), ‖P f k‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hb3 : ∑ f : Fin (r * m), (c * ‖Q (F f) k‖) ^ 2 ≤ 1 / (r : ℝ) := by
      have hpull : ∑ f : Fin (r * m), (c * ‖Q (F f) k‖) ^ 2
          = c ^ 2 * ∑ f : Fin (r * m), ‖Q (F f) k‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun f _ => by ring)
      rw [hpull, hc2]
      calc (((r * m : ℕ) : ℝ))⁻¹ * (∑ f : Fin (r * m), ‖Q (F f) k‖ ^ 2)
          ≤ (((r * m : ℕ) : ℝ))⁻¹ * (m : ℝ) :=
            mul_le_mul_of_nonneg_left (hQF k) (by positivity)
        _ = 1 / (r : ℝ) := by
            push_cast
            field_simp
    have h0 : (0:ℝ) ≤ ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖ := norm_nonneg _
    have hsq : ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖ ^ 2
        ≤ (∑ f : Fin (r * m), (c * ‖Q (F f) k‖) * ‖P f k‖) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self h0 hb
    refine hsq.trans (hb2.trans ?_)
    rw [hPcol k, mul_one]
    exact hb3
  ---- 7.  frobInner as a weighted diagonal sum
  have hfrob : frobInner (shorState (r * m) F) A
      = ∑ k : δ, (Qᴴ * (shorState (r * m) F)ᴴ * P) k k * (s k : ℂ) := by
    subst hA
    rw [frobInner]
    rw [show (shorState (r * m) F)ᴴ * (P * Matrix.diagonal (fun k => (s k : ℂ)) * Qᴴ)
        = ((shorState (r * m) F)ᴴ * P * Matrix.diagonal (fun k => (s k : ℂ))) * Qᴴ from by
      simp [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show Qᴴ * ((shorState (r * m) F)ᴴ * P * Matrix.diagonal (fun k => (s k : ℂ)))
        = (Qᴴ * (shorState (r * m) F)ᴴ * P) * Matrix.diagonal (fun k => (s k : ℂ)) from by
      simp [Matrix.mul_assoc]]
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  ---- 8.  assemble
  have hsum : ‖frobInner (shorState (r * m) F) A‖
      ≤ ∑ k : δ, ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖ * |s k| := by
    rw [hfrob]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsum2 : (∑ k : δ, ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖ * |s k|) ^ 2
      ≤ (∑ k : δ, ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖ ^ 2) * (∑ k : δ, |s k| ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hA1 : ∑ k : δ, ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖ ^ 2
      ≤ (Fintype.card δ : ℝ) / (r : ℝ) := by
    calc ∑ k : δ, ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖ ^ 2
        ≤ ∑ _k : δ, (1 / (r : ℝ)) := Finset.sum_le_sum (fun k _ => hNkk k)
      _ = (Fintype.card δ : ℝ) / (r : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hA2 : ∑ k : δ, |s k| ^ 2 ≤ 1 := by
    have habs : ∀ k : δ, |s k| ^ 2 = s k ^ 2 := fun k => sq_abs _
    rw [Finset.sum_congr rfl (fun k _ => habs k)]
    exact hs
  have h0 : (0:ℝ) ≤ ‖frobInner (shorState (r * m) F) A‖ := norm_nonneg _
  have hsq : ‖frobInner (shorState (r * m) F) A‖ ^ 2
      ≤ (∑ k : δ, ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖ * |s k|) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self h0 hsum
  refine hsq.trans (hsum2.trans ?_)
  have hcard0 : (0:ℝ) ≤ (Fintype.card δ : ℝ) / (r : ℝ) := by positivity
  calc (∑ k : δ, ‖(Qᴴ * (shorState (r * m) F)ᴴ * P) k k‖ ^ 2) * (∑ k : δ, |s k| ^ 2)
      ≤ ((Fintype.card δ : ℝ) / (r : ℝ)) * (∑ k : δ, |s k| ^ 2) :=
        mul_le_mul_of_nonneg_right hA1 (by positivity)
    _ ≤ ((Fintype.card δ : ℝ) / (r : ℝ)) * 1 := mul_le_mul_of_nonneg_left hA2 hcard0
    _ = (Fintype.card δ : ℝ) / (r : ℝ) := mul_one _
