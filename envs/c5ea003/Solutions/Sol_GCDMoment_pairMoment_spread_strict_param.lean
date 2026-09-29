-- Prove2me | solution 1 for GCDMoment.pairMoment_spread_strict_param
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:58:38.959125+00:00
-- url     : https://prove2.me/submissions/06fc25ed-95d5-4a54-a35a-e588db4f83b7

import Mathlib
import Definitions.Def_Novelty_GCDMomentHigherInversion
import Definitions.Def_Novelty_GCDMomentPairInversion

open GCDMoment in
theorem solution {g al ga de : ℤ} (hg : 1 ≤ g) (hal : 1 ≤ al) (hga : 1 ≤ ga) (hde : 1 ≤ de)
    (halga : al < ga) (hgde : g < de) (m : ℕ)
    (hsum : g * al + ga * de + g * ga + al * de < g * al * ga * de) :
    pairMoment (m + 3) (g * ga) (al * de) < pairMoment (m + 3) (g * al) (ga * de) := by
  have hbracket : 0 < (g * al * ga * de) * hSum (m + 1) ga al * hSum (m + 1) de g
      - hSum (m + 2) ga al * hSum (m + 2) de g - 1 := by
    -- the homogeneous sums are positive and dominate their last term
    have hpos : ∀ (n : ℕ) (x y : ℤ), 1 ≤ x → 1 ≤ y → 1 ≤ hSum n x y := by
      intro n
      induction n with
      | zero => intro x y _ _; simp [hSum]
      | succ n ih =>
        intro x y hx hy
        have hprev := ih x y hx hy
        have hyp : 1 ≤ y ^ (n + 1) := one_le_pow₀ hy
        rw [hSum]
        nlinarith
    have hyle : ∀ (n : ℕ) (x y : ℤ), 1 ≤ x → 1 ≤ y → y ^ n ≤ hSum n x y := by
      intro n
      induction n with
      | zero => intro x y _ _; simp [hSum]
      | succ n ih =>
        intro x y hx hy
        have hprev := hpos n x y hx hy
        rw [hSum]
        nlinarith
    have hstep : ∀ (n : ℕ) (x y : ℤ), 1 ≤ x → 1 ≤ y →
        hSum (n + 1) x y ≤ (x + y) * hSum n x y := by
      intro n x y hx hy
      have hprev := hpos n x y hx hy
      have hy1 : y ^ (n + 1) ≤ y * hSum n x y := by
        have hyn := hyle n x y hx hy
        have : y ^ (n + 1) = y * y ^ n := by ring
        rw [this]
        nlinarith
      rw [hSum]
      nlinarith
    have hge2 : ∀ (n : ℕ) (x y : ℤ), 1 ≤ x → 1 ≤ y → 2 ≤ hSum (n + 1) x y := by
      intro n x y hx hy
      have hprev := hpos n x y hx hy
      have hyp : 1 ≤ y ^ (n + 1) := one_le_pow₀ hy
      rw [hSum]
      nlinarith
    -- abbreviations
    set A := hSum (m + 1) ga al with hAdef
    set B := hSum (m + 1) de g with hBdef
    set C := hSum (m + 2) ga al with hCdef
    set D := hSum (m + 2) de g with hDdef
    have hA1 : 1 ≤ A := hpos _ _ _ hga hal
    have hB1 : 1 ≤ B := hpos _ _ _ hde hg
    have hA2 : 2 ≤ A := hge2 _ _ _ hga hal
    have hC1 : 1 ≤ C := hpos _ _ _ hga hal
    have hD1 : 1 ≤ D := hpos _ _ _ hde hg
    have hCle : C ≤ (ga + al) * A := hstep _ _ _ hga hal
    have hDle : D ≤ (de + g) * B := hstep _ _ _ hde hg
    have hgap : (ga + al) * (de + g) + 1 ≤ g * al * ga * de := by nlinarith [hsum]
    have hABpos : (0 : ℤ) ≤ A * B := by nlinarith [hA1, hB1]
    have h1 : C * D ≤ ((ga + al) * (de + g)) * (A * B) := by
      have hmul := mul_le_mul hCle hDle (by linarith) (by nlinarith [hA1, hga, hal])
      calc C * D ≤ ((ga + al) * A) * ((de + g) * B) := hmul
        _ = ((ga + al) * (de + g)) * (A * B) := by ring
    have h2 : ((ga + al) * (de + g)) * (A * B) + (A * B) ≤ (g * al * ga * de) * (A * B) := by
      have hmul := mul_le_mul_of_nonneg_right hgap hABpos
      calc ((ga + al) * (de + g)) * (A * B) + (A * B)
          = ((ga + al) * (de + g) + 1) * (A * B) := by ring
        _ ≤ (g * al * ga * de) * (A * B) := hmul
    have h3 : (2 : ℤ) ≤ A * B := by nlinarith [hA2, hB1]
    have hassoc : (g * al * ga * de) * A * B = (g * al * ga * de) * (A * B) := by ring
    rw [hassoc]
    linarith [h1, h2, h3]
  -- the factorisation of a power difference
  have hfac : ∀ (n : ℕ) (x y : ℤ), (x - y) * hSum n x y = x ^ (n + 1) - y ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro x y
      simp [hSum]
    | succ n ih =>
      intro x y
      rw [hSum]
      linear_combination x * ih x y
  have h1 : (ga - al) * hSum (m + 1) ga al = ga ^ (m + 2) - al ^ (m + 2) := by
    have hx := hfac (m + 1) ga al
    rw [show m + 1 + 1 = m + 2 from rfl] at hx
    exact hx
  have h2 : (de - g) * hSum (m + 1) de g = de ^ (m + 2) - g ^ (m + 2) := by
    have hx := hfac (m + 1) de g
    rw [show m + 1 + 1 = m + 2 from rfl] at hx
    exact hx
  have h3 : (ga - al) * hSum (m + 2) ga al = ga ^ (m + 3) - al ^ (m + 3) := by
    have hx := hfac (m + 2) ga al
    rw [show m + 2 + 1 = m + 3 from rfl] at hx
    exact hx
  have h4 : (de - g) * hSum (m + 2) de g = de ^ (m + 3) - g ^ (m + 3) := by
    have hx := hfac (m + 2) de g
    rw [show m + 2 + 1 = m + 3 from rfl] at hx
    exact hx
  -- the difference of the two pair moments factors through the bracket
  have hid : pairMoment (m + 3) (g * al) (ga * de) - pairMoment (m + 3) (g * ga) (al * de)
      = (ga - al) * (de - g) * ((g * al * ga * de) * hSum (m + 1) ga al * hSum (m + 1) de g
        - hSum (m + 2) ga al * hSum (m + 2) de g - 1) := by
    have hring : pairMoment (m + 3) (g * al) (ga * de) - pairMoment (m + 3) (g * ga) (al * de)
        = (g * al * ga * de) * (ga ^ (m + 2) - al ^ (m + 2)) * (de ^ (m + 2) - g ^ (m + 2))
          - (ga ^ (m + 3) - al ^ (m + 3)) * (de ^ (m + 3) - g ^ (m + 3))
          - (ga - al) * (de - g) := by
      unfold pairMoment
      ring
    rw [hring, ← h1, ← h2, ← h3, ← h4]
    ring
  have hposfac : 0 < (ga - al) * (de - g) := mul_pos (by linarith) (by linarith)
  nlinarith [hid, hbracket, hposfac]
