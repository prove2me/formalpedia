-- Prove2me | solution 1 for RademacherMassart.rad_cube
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:06:55.625616+00:00
-- url     : https://prove2.me/submissions/5fb819e8-642b-4652-94cd-b23bd9578ebf

-- Sol generated from Logic/Rademacher/Massart.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Massart
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




/-! ### Tightness: the full sign cube -/


lemma cube_nonempty (n : ℕ) : (cube n).Nonempty := by
  refine ⟨sgn (fun _ => true), ?_⟩
  simp [cube]




open RademacherMassart in
theorem solution(hn : 0 < n) : rad ((cube n : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) = 1 := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hmax : ∀ ε : Fin n → Bool, maxCorr (cube n) (cube_nonempty n) ε = (n : ℝ) := by
    intro ε
    apply le_antisymm
    · refine Finset.sup'_le _ _ ?_
      rintro v hv
      simp only [cube, Finset.mem_image] at hv
      obtain ⟨δ, -, rfl⟩ := hv
      calc ∑ i, sgn ε i * sgn δ i ≤ ∑ _i : Fin n, (1:ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            simp only [sgn]
            rcases Bool.eq_false_or_eq_true (ε i) with h | h <;>
              rcases Bool.eq_false_or_eq_true (δ i) with h' | h' <;> simp [h, h']
        _ = (n:ℝ) := by simp
    · have hmem : sgn ε ∈ cube n := by simp [cube]
      have := Finset.le_sup' (s := cube n) (fun v : Fin n → ℝ => ∑ i, sgn ε i * v i) hmem
      refine le_trans (le_of_eq ?_) this
      have : ∀ i : Fin n, sgn ε i * sgn ε i = 1 := by
        intro i
        simp only [sgn]
        rcases Bool.eq_false_or_eq_true (ε i) with h | h <;> simp [h]
      simp [this]
  rw [rad_finset (cube n) (cube_nonempty n)]
  rw [Finset.sum_congr rfl fun ε _ => hmax ε]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  field_simp
