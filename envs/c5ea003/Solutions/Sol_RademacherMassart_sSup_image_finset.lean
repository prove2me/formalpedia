-- Prove2me | solution 1 for RademacherMassart.sSup_image_finset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:04:12.431205+00:00
-- url     : https://prove2.me/submissions/f55cec78-1568-4efe-94fc-3e40305aa8a3

-- Sol generated from Logic/Rademacher/Massart.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Massart
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







/-! ### Tightness: the full sign cube -/






open RademacherMassart in
theorem solution(F : Finset (Fin n → ℝ)) (hne : F.Nonempty) (ε : Fin n → Bool) :
    sSup (signAvg ε '' (F : Set (Fin n → ℝ))) = (1 / (n : ℝ)) * maxCorr F hne ε := by
  have hmem : ∃ v ∈ F, F.sup' hne (fun v => ∑ i, sgn ε i * v i) = ∑ i, sgn ε i * v i :=
    Finset.exists_mem_eq_sup' hne _
  obtain ⟨v₀, hv₀, hval⟩ := hmem
  refine IsGreatest.csSup_eq ⟨⟨v₀, hv₀, ?_⟩, ?_⟩
  · unfold signAvg maxCorr
    rw [hval]
  · rintro a ⟨v, hv, rfl⟩
    unfold signAvg maxCorr
    have hle : ∑ i, sgn ε i * v i ≤ F.sup' hne (fun v => ∑ i, sgn ε i * v i) :=
      Finset.le_sup' (fun v : Fin n → ℝ => ∑ i, sgn ε i * v i) hv
    have hn : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hle hn
