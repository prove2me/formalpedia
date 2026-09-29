-- Prove2me | solution 1 for RademacherMassart.rad_le_massart
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:10:13.261724+00:00
-- url     : https://prove2.me/submissions/0f064bc5-9109-4193-8e68-5fc5af998fe6

-- Sol generated from Logic/Rademacher/Massart.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Massart
import Theorems.Thm_RademacherMassart_avg_maxCorr_le
import Theorems.Thm_RademacherMassart_rad_singleton
import Theorems.Thm_RademacherMassart_sSup_image_finset
/-
# Massart's finite class lemma

If a hypothesis class restricted to a sample of size `n` consists of `N` vectors, each
of Euclidean length at most `r`, then its empirical Rademacher complexity is at most

  `r * √(2 log N) / n`.

The proof is the classical Chernoff/MGF argument:

* Jensen's inequality moves the expectation inside the exponential;
* a maximum is bounded by a sum, and the moment generating function of a Rademacher
  sum factorises into hyperbolic cosines, `𝔼 exp(λ⟨σ,v⟩) = ∏ cosh(λ vᵢ)`;
* `cosh t ≤ exp(t²/2)` gives the sub-Gaussian bound `exp(λ²r²/2)`;
* optimising over `λ` yields `√(2 log N)`.

Combined with `Massart` for the class of all `±1` patterns, this shows the bound is
tight up to the absolute constant `√(2 log 2) ≈ 1.177`; see `rad_cube` and
`massart_cube_tight` at the end of the file.

This file is self-contained.
-/

open RademacherMassart

open Finset

variable {n : ℕ}




/-! ### Elementary facts about sign patterns -/





/-! ### The two analytic ingredients -/




/-! ### Massart's lemma -/



/-- The Rademacher complexity of a finite class in terms of `maxCorr`. -/
lemma rad_finset (F : Finset (Fin n → ℝ)) (hne : F.Nonempty) :
    rad (F : Set (Fin n → ℝ))
      = (1 / (n : ℝ)) * ((∑ ε : Fin n → Bool, maxCorr F hne ε) / 2 ^ n) := by
  unfold rad
  rw [Finset.sum_congr rfl fun ε _ => sSup_image_finset F hne ε, ← Finset.mul_sum]
  ring


/-- The optimal choice `λ = √(2 log N)/r` balances the two terms of the Chernoff bound. -/
lemma optimal_lambda {r s L : ℝ} (hr : 0 < r) (hs : 0 < s) (hsq : s * s = 2 * L) :
    L / (s / r) + (s / r) * r ^ 2 / 2 = r * s := by
  field_simp
  nlinarith [hsq]


/-! ### Tightness: the full sign cube -/






open RademacherMassart in
theorem solution(F : Finset (Fin n → ℝ)) (hne : F.Nonempty) (hn : 0 < n)
    {r : ℝ} (hr : 0 ≤ r) (hF : ∀ v ∈ F, ∑ i, (v i) ^ 2 ≤ r ^ 2) :
    rad (F : Set (Fin n → ℝ)) ≤ r * Real.sqrt (2 * Real.log F.card) / n := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  by_cases hcard1 : F.card = 1
  · -- a class with a single element has zero complexity
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard1
    have hFv : (F : Set (Fin n → ℝ)) = ({v} : Set (Fin n → ℝ)) := by rw [hv]; simp
    rw [hFv, rad_singleton, hv]
    simp
  · -- at least two elements: `log N > 0`
    have hcard2 : 2 ≤ F.card := by
      have := Finset.card_pos.mpr hne
      omega
    have hcardR : (2:ℝ) ≤ F.card := by exact_mod_cast hcard2
    have hlogpos : 0 < Real.log F.card := by
      apply Real.log_pos
      linarith
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · -- `r = 0` forces every element to be the zero vector, contradicting `2 ≤ N`
      exfalso
      have hzero : ∀ v ∈ F, v = 0 := by
        intro v hv
        have h := hF v hv
        rw [← hr0] at h
        have hsum : ∑ i, (v i) ^ 2 ≤ 0 := by simpa using h
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp
          (le_antisymm hsum (Finset.sum_nonneg fun i _ => sq_nonneg (v i)))
        funext i
        have := this i (Finset.mem_univ i)
        simpa [pow_eq_zero_iff] using this
      have hsub : F ⊆ {0} := fun v hv => by simp [hzero v hv]
      have := Finset.card_le_card hsub
      simp at this
      omega
    · set L := Real.log F.card with hL
      set l := Real.sqrt (2 * L) / r with hl
      have h2L : 0 < 2 * L := by linarith
      have hsq : Real.sqrt (2 * L) > 0 := Real.sqrt_pos.mpr h2L
      have hlpos : 0 < l := by positivity
      have hbound := avg_maxCorr_le F hne hlpos hF
      have hsqsq : Real.sqrt (2 * L) * Real.sqrt (2 * L) = 2 * L :=
        Real.mul_self_sqrt h2L.le
      have hval : L / l + l * r ^ 2 / 2 = r * Real.sqrt (2 * L) := by
        rw [hl]
        exact optimal_lambda hrpos hsq hsqsq
      rw [hval] at hbound
      rw [rad_finset F hne]
      have hmul := mul_le_mul_of_nonneg_left hbound
        (le_of_lt (by positivity : (0:ℝ) < 1 / (n:ℝ)))
      calc (1 / (n:ℝ)) * ((∑ ε : Fin n → Bool, maxCorr F hne ε) / 2 ^ n)
          ≤ (1 / (n:ℝ)) * (r * Real.sqrt (2 * L)) := hmul
        _ = r * Real.sqrt (2 * L) / n := by ring
