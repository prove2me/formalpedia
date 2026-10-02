-- Prove2me | solution 1 for BookSixth.standard_pair_axis_homeo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T13:38:29.730687+00:00
-- url     : https://prove2.me/submissions/6ddd31e4-e33a-4da9-be5e-936a50da96b5

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

namespace PairRelabelV2

noncomputable section

def tau (t : ℝ) : ℝ := max 0 (min t 1)

theorem tau_zero : tau 0 = 0 := by
  simp [tau]

theorem tau_one : tau 1 = 1 := by
  simp [tau]

theorem tau_nonneg (t : ℝ) : 0 <= tau t := by
  simp [tau]

theorem continuous_tau : Continuous tau := by
  simpa [tau] using
    (continuous_const.max (continuous_id.min continuous_const))

def axisU (a : ℝ) (t : ℝ) : ℝ := a * tau t

def axisV (b : ℝ) (t : ℝ) : ℝ := (3 - b) * tau t

def axisW (a b : ℝ) (t : ℝ) : ℝ :=
  1 - axisU a t - axisV b t

def axisA (a b : ℝ) (t : ℝ) : ℝ := 1 + axisU a t

def axisB (a b : ℝ) (t : ℝ) : ℝ := 2 - axisV b t

def axisF (a b : ℝ) (t x : ℝ) : ℝ :=
  if x <= axisA a b t then x - axisU a t
  else if x <= axisB a b t then
    1 + (x - axisA a b t) / axisW a b t
  else x + axisV b t

def axisG (a b : ℝ) (t y : ℝ) : ℝ :=
  if y <= 1 then y + axisU a t
  else if y <= 2 then
    axisA a b t + (y - 1) * axisW a b t
  else y - axisV b t

theorem axisW_pos {a b : ℝ} (hab : 3 <= b - a) (t : ℝ) :
    0 < axisW a b t := by
  have hcoef : 0 <= b - a - 3 := by linarith
  have hmul : 0 <= (b - a - 3) * tau t :=
    mul_nonneg hcoef (tau_nonneg t)
  have heq : axisW a b t = 1 + (b - a - 3) * tau t := by
    dsimp [axisW, axisU, axisV]
    ring
  rw [heq]
  nlinarith

theorem axisG_continuous {a b : ℝ} (hab : 3 <= b - a) (t : ℝ) :
    Continuous (axisG a b t) := by
  have hw : 0 < axisW a b t := axisW_pos hab t
  have hgap : axisB a b t - axisA a b t = axisW a b t := by
    dsimp [axisA, axisB, axisW, axisU, axisV]
    ring
  have hAB : axisA a b t <= axisB a b t := by
    linarith
  have hG_low : Continuous (fun y : ℝ => y + axisU a t) := by
    exact continuous_id.add continuous_const
  have hG_mid : Continuous
      (fun y : ℝ => axisA a b t + (y - 1) * axisW a b t) := by
    have hy : Continuous (fun y : ℝ => y - 1) := by
      exact continuous_id.sub continuous_const
    have hw : Continuous (fun _ : ℝ => axisW a b t) :=
      continuous_const
    have hmul : Continuous
        (fun y : ℝ => (y - 1) * axisW a b t) :=
      hy.mul hw
    exact continuous_const.add hmul
  have hG_high : Continuous (fun y : ℝ => y - axisV b t) := by
    exact continuous_id.sub continuous_const
  have hG_upper : Continuous
      (fun y : ℝ => if y <= 2 then
        axisA a b t + (y - 1) * axisW a b t
      else y - axisV b t) := by
    exact continuous_if_le continuous_id continuous_const
      hG_mid.continuousOn hG_high.continuousOn (by
        intro y hy
        have hy2 : y = 2 := by simpa using hy
        subst y
        dsimp [axisA, axisB, axisW, axisU, axisV]
        ring)
  have hG : Continuous
      (fun y : ℝ => if y <= 1 then y + axisU a t
        else if y <= 2 then
          axisA a b t + (y - 1) * axisW a b t
        else y - axisV b t) := by
    exact continuous_if_le continuous_id continuous_const
      hG_low.continuousOn hG_upper.continuousOn (by
        intro y hy
        have hy1 : y = 1 := by
          simpa using hy
        subst y
        have h12 : (1 : ℝ) ≤ 2 := by norm_num
        simp only [if_pos h12]
        dsimp [axisA, axisB, axisW, axisU, axisV]
        ring)
  simpa [axisG] using hG

theorem axisF_axisG {a b : ℝ} (hab : 3 <= b - a) (t y : ℝ) :
    axisF a b t (axisG a b t y) = y := by
  have hw : 0 < axisW a b t := axisW_pos hab t
  by_cases hy1 : y <= 1
  · have hya : y + axisU a t <= axisA a b t := by
      dsimp [axisA]
      linarith
    simpa [axisG, axisF, hy1, hya] using
      (sub_add_cancel y (axisU a t))
  · by_cases hy2 : y <= 2
    · have hratio0 : 0 < (y - 1) * axisW a b t := by
        exact mul_pos (sub_pos.mpr (lt_of_not_ge hy1)) hw
      have hxa : axisA a b t <
          axisA a b t + (y - 1) * axisW a b t := by
        nlinarith
      have hmul : y - 1 <= 1 := by linarith
      have hmul' := mul_le_mul_of_nonneg_right hmul (le_of_lt hw)
      have hgap : axisB a b t - axisA a b t = axisW a b t := by
        dsimp [axisA, axisB, axisW, axisU, axisV]
        ring
      have hxb : axisA a b t + (y - 1) * axisW a b t <=
          axisB a b t := by
        nlinarith
      dsimp only [axisG, axisF]
      rw [if_neg hy1,
        if_pos hy2,
        if_neg (not_le.mpr hxa),
        if_pos hxb]
      field_simp [ne_of_gt hw]
      ring
    · have hyb : axisB a b t < y - axisV b t := by
        dsimp [axisB, axisV]
        linarith
      have hAB : axisA a b t <= axisB a b t := by
        have hgap := axisW_pos hab t
        dsimp [axisA, axisB, axisW, axisU, axisV] at hgap ⊢
        linarith
      have hnotA : ¬ y - axisV b t <= axisA a b t := by
        linarith
      have hnotB : ¬ y - axisV b t <= axisB a b t :=
        not_le.mpr hyb
      dsimp only [axisG, axisF]
      rw [if_neg hy1, if_neg hy2, if_neg hnotA, if_neg hnotB]
      ring

theorem axisG_axisF {a b : ℝ} (hab : 3 <= b - a) (t x : ℝ) :
    axisG a b t (axisF a b t x) = x := by
  have hw : 0 < axisW a b t := axisW_pos hab t
  by_cases hx1 : x <= axisA a b t
  · have hxf : axisF a b t x = x - axisU a t := by
      rw [axisF, if_pos hx1]
    have hxf_le : axisF a b t x <= 1 := by
      rw [hxf]
      have hA : x <= 1 + axisU a t := by
        simpa [axisA] using hx1
      linarith
    rw [axisG, if_pos hxf_le, hxf]
    ring
  · by_cases hx2 : x <= axisB a b t
    · have hxa : axisA a b t < x := by linarith
      have hgap : axisB a b t - axisA a b t = axisW a b t := by
        dsimp [axisA, axisB, axisW, axisU, axisV]
        ring
      have hratio0 : 0 < (x - axisA a b t) / axisW a b t := by
        apply (lt_div_iff₀ hw).2
        nlinarith
      have hratio1 : (x - axisA a b t) / axisW a b t <= 1 := by
        apply (div_le_iff₀ hw).2
        nlinarith
      have hxf :
          axisF a b t x = 1 + (x - axisA a b t) / axisW a b t := by
        rw [axisF, if_neg hx1, if_pos hx2]
      have hxf1 : 1 < axisF a b t x := by
        rw [hxf]
        linarith
      have hxf2 : axisF a b t x <= 2 := by
        rw [hxf]
        linarith
      rw [axisG, if_neg (not_le.mpr hxf1), if_pos hxf2]
      rw [hxf]
      field_simp [ne_of_gt hw]
      ring
    · have hgap : axisB a b t - axisA a b t = axisW a b t := by
        dsimp [axisA, axisB, axisW, axisU, axisV]
        ring
      have hratio : 1 < (x - axisA a b t) / axisW a b t := by
        apply (lt_div_iff₀ hw).2
        nlinarith
      have hxB : axisB a b t < x := by
        have hnum := (lt_div_iff₀ hw).mp hratio
        linarith [hgap]
      have hBV : axisB a b t + axisV b t = 2 := by
        dsimp [axisB, axisV, axisU]
        ring
      have hxf : axisF a b t x = x + axisV b t := by
        rw [axisF, if_neg hx1, if_neg hx2]
      have hxf2 : 2 < axisF a b t x := by
        rw [hxf]
        linarith [hxB, hBV]
      have hnot1 : ¬ axisF a b t x <= 1 := by
        intro h1
        linarith
      have hnot2 : ¬ axisF a b t x <= 2 := by
        intro h2
        linarith
      rw [axisG, if_neg hnot1, if_neg hnot2]
      rw [hxf]
      ring

theorem axisF_right_strict {a b : ℝ} (hb : 3 <= b) (hab : 3 <= b - a)
    {t x : ℝ} (hx : axisB a b t < x) :
    axisF a b t x = x + axisV b t := by
  have hw : 0 < axisW a b t := axisW_pos hab t
  have hAB : axisA a b t <= axisB a b t := by
    have hgap : axisB a b t - axisA a b t = axisW a b t := by
      dsimp [axisA, axisB, axisW, axisU, axisV]
      ring
    linarith [hw, hgap]
  have hA : ¬ x <= axisA a b t := by
    intro hxA
    exact (not_lt_of_ge hAB) (lt_of_lt_of_le hx hxA)
  have hB : ¬ x <= axisB a b t := not_le.mpr hx
  simp [axisF, hA, hB]

theorem axisF_atB {a b : ℝ} (hab : 3 <= b - a) (t : ℝ) :
    axisF a b t (axisB a b t) = 2 := by
  have hw : 0 < axisW a b t := axisW_pos hab t
  have hgap : axisB a b t - axisA a b t = axisW a b t := by
    dsimp [axisA, axisB, axisW, axisU, axisV]
    ring
  have hBA : axisA a b t < axisB a b t := by
    linarith [hw, hgap]
  have hA : ¬ axisB a b t <= axisA a b t := not_le.mpr hBA
  rw [axisF, if_neg hA, if_pos (le_refl (axisB a b t))]
  rw [hgap]
  field_simp [ne_of_gt hw] <;> ring

theorem axisF_zero {a b : ℝ} (hab : 3 <= b - a) (x : ℝ) :
    axisF a b 0 x = x := by
  have hA : axisA a b 0 = 1 := by
    simp [axisA, axisU, tau_zero]
  have hB : axisB a b 0 = 2 := by
    simp [axisB, axisV, tau_zero]
  have hW : axisW a b 0 = 1 := by
    simp [axisW, axisU, axisV, tau_zero]
  by_cases hx1 : x <= axisA a b 0
  · simp [axisF, hx1, axisU, tau_zero]
  · by_cases hx2 : x <= axisB a b 0
    · simp [axisF, hx1, hx2, axisA, axisB, axisW, axisU, axisV, tau_zero]
    · simp [axisF, hx1, hx2, axisV, tau_zero]

theorem axisF_one_left {a b : ℝ} (ha : 0 <= a) (hab : 3 <= b - a)
    {u : ℝ} (hlo : -1 <= u) (hhi : u <= 1) :
    axisF a b 1 (a + u) = u := by
  have hA : a + u <= axisA a b 1 := by
    have hupper : a + u <= a + 1 := by linarith
    simpa [axisA, axisU, tau_one, add_comm] using hupper
  rw [axisF, if_pos hA]
  simp [axisU, tau_one]

theorem axisF_one_right {a b : ℝ} (hb : 3 <= b) (hab : 3 <= b - a)
    {u : ℝ} (hlo : -1 <= u) (hhi : u <= 1) :
    axisF a b 1 (b + u) = 3 + u := by
  have hB : axisB a b 1 = b - 1 := by
    simp only [axisB, axisV, tau_one]
    ring
  by_cases hu : u = -1
  · subst u
    calc
      axisF a b 1 (b + (-1 : ℝ)) = axisF a b 1 (axisB a b 1) := by
        rw [hB]
        ring
      _ = 2 := axisF_atB hab 1
      _ = 3 + (-1 : ℝ) := by norm_num
  · have hu' : -1 < u := lt_of_le_of_ne hlo (Ne.symm hu)
    have hx : axisB a b 1 < b + u := by
      rw [hB]
      linarith
    have hf := axisF_right_strict (t := 1) hb hab hx
    have hf' : axisF a b 1 (b + u) = b + u + (3 - b) := by
      simpa [axisV, tau_one, mul_one] using hf
    calc
      axisF a b 1 (b + u) = b + u + (3 - b) := hf'
      _ = 3 + u := by ring

theorem axisF_family_continuous {a b : ℝ} (hab : 3 <= b - a) :
    Continuous (fun p : ℝ × ℝ => axisF a b p.1 p.2) := by
  have hU : Continuous (fun p : ℝ × ℝ => axisU a p.1) := by
    change Continuous (fun p : ℝ × ℝ => a * tau p.1)
    simpa [Function.comp_def] using
      (continuous_const.mul continuous_tau).comp continuous_fst
  have hV : Continuous (fun p : ℝ × ℝ => axisV b p.1) := by
    change Continuous (fun p : ℝ × ℝ => (3 - b) * tau p.1)
    simpa [Function.comp_def] using
      (continuous_const.mul continuous_tau).comp continuous_fst
  have hW : Continuous (fun p : ℝ × ℝ => axisW a b p.1) := by
    simpa [axisW] using
      ((continuous_const :
        Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).sub hU).sub hV
  have hA : Continuous (fun p : ℝ × ℝ => axisA a b p.1) := by
    change Continuous (fun p : ℝ × ℝ => 1 + axisU a p.1)
    exact continuous_const.add hU
  have hB : Continuous (fun p : ℝ × ℝ => axisB a b p.1) := by
    change Continuous (fun p : ℝ × ℝ => 2 - axisV b p.1)
    exact continuous_const.sub hV
  have hlow : Continuous
      (fun p : ℝ × ℝ => p.2 - axisU a p.1) :=
    continuous_snd.sub hU
  have hmid : Continuous
      (fun p : ℝ × ℝ =>
        1 + (p.2 - axisA a b p.1) / axisW a b p.1) :=
    continuous_const.add
      ((continuous_snd.sub hA).div hW
        (fun p => ne_of_gt (axisW_pos hab p.1)))
  have hhigh : Continuous
      (fun p : ℝ × ℝ => p.2 + axisV b p.1) :=
    continuous_snd.add hV
  have hupper : Continuous
      (fun p : ℝ × ℝ =>
        if p.2 <= axisB a b p.1 then
          1 + (p.2 - axisA a b p.1) / axisW a b p.1
        else p.2 + axisV b p.1) := by
    exact continuous_if_le (f := fun p : ℝ × ℝ => p.2)
      (g := fun p : ℝ × ℝ => axisB a b p.1)
      continuous_snd hB hmid.continuousOn hhigh.continuousOn (by
        intro p hp
        have hpB : p.2 = axisB a b p.1 := by simpa using hp
        rw [hpB]
        have hw : 0 < axisW a b p.1 := axisW_pos hab p.1
        have hright : axisB a b p.1 + axisV b p.1 = 2 := by
          simp [axisB, axisV, axisU]
        have hleft :
            1 + (axisB a b p.1 - axisA a b p.1) / axisW a b p.1 = 2 := by
          have hgap : axisB a b p.1 - axisA a b p.1 = axisW a b p.1 := by
            dsimp [axisA, axisB, axisW, axisU, axisV]
            ring
          rw [hgap]
          field_simp [ne_of_gt hw] <;> ring
        exact hleft.trans hright.symm)
  have h := continuous_if_le
    (f := fun p : ℝ × ℝ => p.2)
    (g := fun p : ℝ × ℝ => axisA a b p.1)
    (f' := fun p : ℝ × ℝ => p.2 - axisU a p.1)
    (g' := fun p : ℝ × ℝ =>
      if p.2 <= axisB a b p.1 then
        1 + (p.2 - axisA a b p.1) / axisW a b p.1
      else p.2 + axisV b p.1)
    continuous_snd hA hlow.continuousOn hupper.continuousOn (by
      intro p hp
      have hpA : p.2 = axisA a b p.1 := by simpa using hp
      change p.2 - axisU a p.1 =
        (if p.2 <= axisB a b p.1 then
          1 + (p.2 - axisA a b p.1) / axisW a b p.1
          else p.2 + axisV b p.1)
      simp only [hpA]
      have hw : 0 < axisW a b p.1 := axisW_pos hab p.1
      have hAB : axisA a b p.1 <= axisB a b p.1 := by
        have hgap : axisB a b p.1 - axisA a b p.1 = axisW a b p.1 := by
          dsimp [axisA, axisB, axisW, axisU, axisV]
          ring
        linarith
      rw [if_pos hAB]
      dsimp [axisA, axisW, axisU, axisV]
      field_simp [ne_of_gt hw]
      ring)
  simpa [axisF] using h

theorem axisG_family_continuous {a b : ℝ} (hab : 3 <= b - a) :
    Continuous (fun p : ℝ × ℝ => axisG a b p.1 p.2) := by
  have hU : Continuous (fun p : ℝ × ℝ => axisU a p.1) := by
    change Continuous (fun p : ℝ × ℝ => a * tau p.1)
    simpa [Function.comp_def] using
      (continuous_const.mul continuous_tau).comp continuous_fst
  have hV : Continuous (fun p : ℝ × ℝ => axisV b p.1) := by
    change Continuous (fun p : ℝ × ℝ => (3 - b) * tau p.1)
    simpa [Function.comp_def] using
      (continuous_const.mul continuous_tau).comp continuous_fst
  have hW : Continuous (fun p : ℝ × ℝ => axisW a b p.1) := by
    simpa [axisW] using
      ((continuous_const :
        Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).sub hU).sub hV
  have hA : Continuous (fun p : ℝ × ℝ => axisA a b p.1) := by
    change Continuous (fun p : ℝ × ℝ => 1 + axisU a p.1)
    exact continuous_const.add hU
  have hlow : Continuous
      (fun p : ℝ × ℝ => p.2 + axisU a p.1) :=
    continuous_snd.add hU
  have hmid : Continuous
      (fun p : ℝ × ℝ =>
        axisA a b p.1 + (p.2 - 1) * axisW a b p.1) :=
    hA.add ((continuous_snd.sub continuous_const).mul hW)
  have hhigh : Continuous
      (fun p : ℝ × ℝ => p.2 - axisV b p.1) :=
    continuous_snd.sub hV
  have hupper : Continuous
      (fun p : ℝ × ℝ =>
        if p.2 <= 2 then
          axisA a b p.1 + (p.2 - 1) * axisW a b p.1
        else p.2 - axisV b p.1) := by
    exact continuous_if_le (f := fun p : ℝ × ℝ => p.2)
      (g := fun _ : ℝ × ℝ => (2 : ℝ))
      continuous_snd continuous_const hmid.continuousOn hhigh.continuousOn (by
        intro p hp
        have hp2 : p.2 = 2 := by simpa using hp
        rw [hp2]
        calc
          axisA a b p.1 + (2 - 1) * axisW a b p.1 =
              2 - axisV b p.1 := by
            dsimp [axisA, axisW, axisU, axisV]
            ring
          _ = 2 - axisV b p.1 := rfl)
  have h := continuous_if_le
    (f := fun p : ℝ × ℝ => p.2)
    (g := fun _ : ℝ × ℝ => (1 : ℝ))
    (f' := fun p : ℝ × ℝ => p.2 + axisU a p.1)
    (g' := fun p : ℝ × ℝ =>
      if p.2 <= 2 then
        axisA a b p.1 + (p.2 - 1) * axisW a b p.1
      else p.2 - axisV b p.1)
    continuous_snd continuous_const hlow.continuousOn hupper.continuousOn (by
      intro p hp
      have hp1 : p.2 = 1 := by simpa using hp
      change p.2 + axisU a p.1 =
        (if p.2 <= 2 then
          axisA a b p.1 + (p.2 - 1) * axisW a b p.1
          else p.2 - axisV b p.1)
      simp only [hp1]
      rw [if_pos (show (1 : ℝ) <= 2 by norm_num)]
      dsimp [axisA, axisW, axisU, axisV]
      ring)
  simpa [axisG] using h

theorem axisF_continuous {a b : ℝ} (hab : 3 <= b - a) (t : ℝ) :
    Continuous (axisF a b t) := by
  exact (axisF_family_continuous hab).comp
    (continuous_const.prodMk continuous_id)

noncomputable def axisHomeo (a b : ℝ) (hab : 3 <= b - a) (t : ℝ) :
    ℝ ≃ₜ ℝ where
  toFun := axisF a b t
  invFun := axisG a b t
  left_inv := axisG_axisF hab t
  right_inv := axisF_axisG hab t
  continuous_toFun := axisF_continuous hab t
  continuous_invFun := axisG_continuous hab t

end

end PairRelabelV2

open PairRelabelV2

theorem solution (a b : ℝ) (ha : 0 <= a) (hb : 3 <= b)
    (hab : 3 <= b - a) :
    ∃ R : ℝ → ℝ ≃ₜ ℝ,
      Continuous (fun p : ℝ × ℝ => R p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => (R p.1).symm p.2) ∧
      (∀ x, R 0 x = x) ∧
      (∀ u, -1 <= u → u <= 1 → R 1 (a + u) = u) ∧
      (∀ u, -1 <= u → u <= 1 → R 1 (b + u) = 3 + u) := by
  let R : ℝ → ℝ ≃ₜ ℝ := fun t => axisHomeo a b hab t
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · change Continuous (fun p : ℝ × ℝ => axisF a b p.1 p.2)
    exact axisF_family_continuous hab
  · change Continuous (fun p : ℝ × ℝ => axisG a b p.1 p.2)
    exact axisG_family_continuous hab
  · intro x
    change axisF a b 0 x = x
    exact axisF_zero hab x
  · intro u hlo hhi
    change axisF a b 1 (a + u) = u
    exact axisF_one_left ha hab hlo hhi
  · intro u hlo hhi
    change axisF a b 1 (b + u) = 3 + u
    exact axisF_one_right hb hab hlo hhi
