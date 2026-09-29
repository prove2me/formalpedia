-- Prove2me | solution 1 for RademacherMassart.avg_maxCorr_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:04:11.843616+00:00
-- url     : https://prove2.me/submissions/d04e1e18-a669-497c-881d-88e9581be2cd

-- Sol generated from Logic/Rademacher/Massart.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Massart
import Theorems.Thm_RademacherMassart_exp_avg_le
import Theorems.Thm_RademacherMassart_prod_exp_le
import Theorems.Thm_RademacherMassart_sum_exp_signed
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
theorem solution(F : Finset (Fin n → ℝ)) (hne : F.Nonempty) {r l : ℝ}
    (hl : 0 < l) (hF : ∀ v ∈ F, ∑ i, (v i) ^ 2 ≤ r ^ 2) :
    (∑ ε : Fin n → Bool, maxCorr F hne ε) / 2 ^ n
      ≤ Real.log F.card / l + l * r ^ 2 / 2 := by
  classical
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  set A := (∑ ε : Fin n → Bool, maxCorr F hne ε) / 2 ^ n with hA
  -- bound the exponential moment
  have hstep1 : Real.exp (l * A)
      ≤ (∑ ε : Fin n → Bool, Real.exp (l * maxCorr F hne ε)) / 2 ^ n := by
    have : l * A = (∑ ε : Fin n → Bool, l * maxCorr F hne ε) / 2 ^ n := by
      rw [← Finset.mul_sum, hA]; ring
    rw [this]
    exact exp_avg_le _
  have hstep2 : ∀ ε : Fin n → Bool, Real.exp (l * maxCorr F hne ε)
      ≤ ∑ v ∈ F, Real.exp (l * ∑ i, sgn ε i * v i) := by
    intro ε
    obtain ⟨v₀, hv₀, hval⟩ := Finset.exists_mem_eq_sup' hne (fun v => ∑ i, sgn ε i * v i)
    have : Real.exp (l * maxCorr F hne ε) = Real.exp (l * ∑ i, sgn ε i * v₀ i) := by
      unfold maxCorr; rw [hval]
    rw [this]
    exact Finset.single_le_sum (f := fun v => Real.exp (l * ∑ i, sgn ε i * v i))
      (fun v _ => (Real.exp_pos _).le) hv₀
  have hstep3 : ∑ ε : Fin n → Bool, Real.exp (l * maxCorr F hne ε)
      ≤ 2 ^ n * (F.card * Real.exp (l ^ 2 * r ^ 2 / 2)) := by
    calc ∑ ε : Fin n → Bool, Real.exp (l * maxCorr F hne ε)
        ≤ ∑ ε : Fin n → Bool, ∑ v ∈ F, Real.exp (l * ∑ i, sgn ε i * v i) :=
          Finset.sum_le_sum fun ε _ => hstep2 ε
      _ = ∑ v ∈ F, ∑ ε : Fin n → Bool, Real.exp (l * ∑ i, sgn ε i * v i) :=
          Finset.sum_comm
      _ ≤ ∑ _v ∈ F, 2 ^ n * Real.exp (l ^ 2 * r ^ 2 / 2) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [sum_exp_signed v l]
          calc ∏ i, (Real.exp (l * v i) + Real.exp (-(l * v i)))
              ≤ 2 ^ n * Real.exp (l ^ 2 * (∑ i, (v i) ^ 2) / 2) := prod_exp_le v l
            _ ≤ 2 ^ n * Real.exp (l ^ 2 * r ^ 2 / 2) := by
                have hmono : l ^ 2 * (∑ i, (v i) ^ 2) / 2 ≤ l ^ 2 * r ^ 2 / 2 := by
                  have := hF v hv
                  nlinarith [sq_nonneg l]
                have := Real.exp_le_exp.mpr hmono
                nlinarith [Real.exp_pos (l ^ 2 * (∑ i, (v i) ^ 2) / 2), (by positivity : (0:ℝ) < 2 ^ n)]
      _ = 2 ^ n * (F.card * Real.exp (l ^ 2 * r ^ 2 / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hcard : (0:ℝ) < F.card := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hexp : Real.exp (l * A) ≤ F.card * Real.exp (l ^ 2 * r ^ 2 / 2) := by
    calc Real.exp (l * A)
        ≤ (∑ ε : Fin n → Bool, Real.exp (l * maxCorr F hne ε)) / 2 ^ n := hstep1
      _ ≤ (2 ^ n * (F.card * Real.exp (l ^ 2 * r ^ 2 / 2))) / 2 ^ n := by
          exact div_le_div_of_nonneg_right hstep3 hpow.le
      _ = F.card * Real.exp (l ^ 2 * r ^ 2 / 2) := by field_simp
  have hlog : l * A ≤ Real.log F.card + l ^ 2 * r ^ 2 / 2 := by
    have hrhs : (F.card : ℝ) * Real.exp (l ^ 2 * r ^ 2 / 2)
        = Real.exp (Real.log F.card + l ^ 2 * r ^ 2 / 2) := by
      rw [Real.exp_add, Real.exp_log hcard]
    rw [hrhs] at hexp
    exact Real.exp_le_exp.mp hexp
  rw [div_add' _ _ _ hl.ne', le_div_iff₀ hl]
  nlinarith [hlog]
