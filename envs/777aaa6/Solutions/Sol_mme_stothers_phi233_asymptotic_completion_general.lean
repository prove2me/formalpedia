-- Prove2me | solution 1 for mme_stothers_phi233_asymptotic_completion_general
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T08:39:11.550215+00:00
-- url     : https://prove2.me/submissions/de0f4258-e904-4ced-a473-8fa4b58d3623

import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_stothers_phi233_profile_data
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic
import Theorems.Thm_mme_finite_word_family_histogram_entropy_upper
import Theorems.Thm_mme_stothers_phi233_entropy_tangent_stability
import Theorems.Thm_mme_stothers_phi233_exact_integer_profile_rounding
import Theorems.Thm_mme_stothers_phi233_exact_profile_entropy_polynomial_lower
import Theorems.Thm_mme_stothers_phi233_integer_histogram_normalization
import Theorems.Thm_mme_stothers_phi233_log_stationarity_of_critical_product
import Theorems.Thm_mme_stothers_phi233_marginal_address_label_histogram
import Theorems.Thm_mme_stothers_phi233_orbit_average_constraints
import Theorems.Thm_mme_stothers_phi233_orbit_entropy_symmetrization
import Theorems.Thm_mme_stothers_phi233_pattern_injective
import Theorems.Thm_mme_stothers_phi233_stationary_profile_sequence_exists
import Theorems.Thm_mme_stothers_phi233_uniform_entropy_stability

open MME BigOperators Filter


open BigOperators
set_option autoImplicit false

/-- A positive stationary profile maximizes entropy at its marginals,
without bounds on those marginals. -/
theorem phi233_full_entropy_upper_of_stationary
    (a b c d sigma mu : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotalProfile : 2 * a + b + c + d = 1)
    (hab : 2 * a + b = sigma) (hac : a + c = mu)
    (hstation :
      2 * (-Real.log (a / 2) - 1) - 2 * (-Real.log (b / 2) - 1) -
        (-Real.log (c / 2) - 1) + (-Real.log (d / 2) - 1) = 0) :
    ∀ x : Fin 10 → ℝ,
      (∀ r, 0 ≤ x r) → (∑ r : Fin 10, x r) = 1 →
      x 0 + x 1 + x 2 = sigma / 2 →
      x 7 + x 8 + x 9 = sigma / 2 →
      x 3 + x 7 = mu / 2 → x 2 + x 6 = mu / 2 →
      x 6 + x 9 = mu / 2 → x 0 + x 3 = mu / 2 →
      (∑ r : Fin 10, Real.negMulLog (x r)) ≤
        4 * Real.negMulLog (a / 2) + 2 * Real.negMulLog (b / 2) +
        2 * Real.negMulLog (c / 2) + 2 * Real.negMulLog (d / 2) := by
  intro x hx htotal hsigma0 hsigma2 hmuJ0 hmuJ3 hmuK0 hmuK3
  let A := (x 0 + x 2 + x 7 + x 9) / 2
  let B := x 1 + x 8
  let C := x 3 + x 6
  let D := x 4 + x 5
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith [hx 0, hx 2, hx 7, hx 9]
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [hx 1, hx 8]
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [hx 3, hx 6]
  have hD : 0 ≤ D := by
    dsimp [D]
    linarith [hx 4, hx 5]
  have horbitConstraints :=
    mme_stothers_phi233_orbit_average_constraints
      x sigma mu
      htotal hsigma0 hsigma2 hmuJ0 hmuJ3 hmuK0 hmuK3
  dsimp only at horbitConstraints
  have hABCD : 2 * A + B + C + D = 1 := by
    simpa only [A, B, C, D] using horbitConstraints.1
  have hAB : 2 * A + B = sigma := by
    simpa only [A, B, C, D] using horbitConstraints.2.1
  have hAC : A + C = mu := by
    simpa only [A, B, C, D] using horbitConstraints.2.2
  have htangent := mme_stothers_phi233_entropy_tangent_stability
    a b c d A B C D sigma mu sigma mu ha hb hc hd hA hB hC hD
    htotalProfile hABCD hab hac hAB hAC hstation
  have horbit := mme_stothers_phi233_orbit_entropy_symmetrization x hx
  have hOrbitRewrite :
      4 * Real.negMulLog ((x 0 + x 2 + x 7 + x 9) / 4) +
          2 * Real.negMulLog ((x 1 + x 8) / 2) +
          2 * Real.negMulLog ((x 3 + x 6) / 2) +
          2 * Real.negMulLog ((x 4 + x 5) / 2) =
        4 * Real.negMulLog (A / 2) +
          2 * Real.negMulLog (B / 2) +
          2 * Real.negMulLog (C / 2) +
          2 * Real.negMulLog (D / 2) := by
    have hAarg : (x 0 + x 2 + x 7 + x 9) / 4 = A / 2 := by
      dsimp [A]
      ring
    have hBarg : (x 1 + x 8) / 2 = B / 2 := by rfl
    have hCarg : (x 3 + x 6) / 2 = C / 2 := by rfl
    have hDarg : (x 4 + x 5) / 2 = D / 2 := by rfl
    rw [hAarg, hBarg, hCarg, hDarg]
  rw [hOrbitRewrite] at horbit
  exact horbit.trans (by simpa using htangent)



theorem phi233_marginal_entropy_upper_general
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (sigma mu a b c d : ℝ)
    (hsigmaRatio : ((2 * alpha + beta : ℕ) : ℝ) / (N : ℝ) = sigma)
    (hmuRatio : ((alpha + gamma : ℕ) : ℝ) / (N : ℝ) = mu)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hab : 2 * a + b = sigma) (hac : a + c = mu)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0) :
    (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) : ℝ) ≤
      (((2 * N + 1 : ℕ) : ℝ)) ^ 10 *
        Real.exp (((2 * N : ℕ) : ℝ) *
          (4 * Real.negMulLog (a / 2) +
            2 * Real.negMulLog (b / 2) +
            2 * Real.negMulLog (c / 2) +
            2 * Real.negMulLog (d / 2))) := by
  classical
  let ftProfile : Fintype
      (MME.StothersFourth.Phi233.ProfileAddress N) := Pi.instFintype
  letI : Fintype
      (MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta) :=
    @Subtype.fintype _ _ (Classical.decPred _) ftProfile
  have hmax := phi233_full_entropy_upper_of_stationary
    a b c d sigma mu ha hb hc hd htotal hab hac hstation
  let labelAt
      (x : MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta) (j : Fin (2 * N)) : Fin 10 :=
    Classical.choose (x.2.1 j)
  have hlabelAt : ∀
      (x : MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta) (i : Fin 3) (j : Fin (2 * N)),
      x.1 i j =
        MME.StothersFourth.Phi233.pattern (labelAt x j) i := by
    intro x i j
    exact congrFun (Classical.choose_spec (x.2.1 j)) i
  have hlabelInjective : Function.Injective labelAt := by
    intro x y hxy
    apply Subtype.ext
    funext i j
    rw [hlabelAt x i j, hxy, ← hlabelAt y i j]
  let F : Finset (Fin (2 * N) → Fin 10) :=
    Finset.univ.image labelAt
  have hFcard : F.card =
      Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) := by
    calc
      F.card =
          (Finset.univ : Finset
            (MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta)).card := by
        exact Finset.card_image_of_injective _ hlabelInjective
      _ = Fintype.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) := Finset.card_univ
      _ = Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) := Nat.card_eq_fintype_card.symm
  let T : ℝ :=
    4 * Real.negMulLog (a / 2) +
      2 * Real.negMulLog (b / 2) +
      2 * Real.negMulLog (c / 2) +
      2 * Real.negMulLog (d / 2)
  have hEntropy : ∀ f ∈ F,
      mme_modern_entropyBits
          (fun r ↦
            (Fintype.card {t : Fin (2 * N) // f t = r} : ℝ) /
              ((2 * N : ℕ) : ℝ)) ≤ T / Real.log 2 := by
    intro f hf
    obtain ⟨x, _hxUniv, hxf⟩ := Finset.mem_image.mp hf
    subst f
    obtain ⟨g, hgcoord, hgtotal, hgsigma0, hgsigma2,
        hgmuJ0, hgmuJ3, hgmuK0, hgmuK3⟩ :=
      mme_stothers_phi233_marginal_address_label_histogram
        N alpha beta gamma delta x
    have hgeq : g = labelAt x := by
      funext j
      apply mme_stothers_phi233_pattern_injective
      funext i
      exact (hgcoord i j).symm.trans (hlabelAt x i j)
    subst g
    let w : Fin 10 → ℕ := fun r ↦
      Fintype.card {t : Fin (2 * N) // labelAt x t = r}
    have hw : ∀ r : Fin 10,
        w r = ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun t ↦ labelAt x t = r)).card := by
      intro r
      dsimp only [w]
      exact Fintype.card_subtype (fun t : Fin (2 * N) ↦ labelAt x t = r)
    have hwtotal : (∑ r : Fin 10, w r) = 2 * N := by
      calc
        (∑ r : Fin 10, w r) =
            ∑ r : Fin 10,
              ((Finset.univ : Finset (Fin (2 * N))).filter
                (fun t ↦ labelAt x t = r)).card := by
          exact Finset.sum_congr rfl (fun r _ ↦ hw r)
        _ = 2 * N := hgtotal
    have hwsigma0 : w 0 + w 1 + w 2 = 2 * alpha + beta := by
      rw [hw 0, hw 1, hw 2]
      exact hgsigma0
    have hwsigma2 : w 7 + w 8 + w 9 = 2 * alpha + beta := by
      rw [hw 7, hw 8, hw 9]
      exact hgsigma2
    have hwmuJ0 : w 3 + w 7 = alpha + gamma := by
      rw [hw 3, hw 7]
      exact hgmuJ0
    have hwmuJ3 : w 2 + w 6 = alpha + gamma := by
      rw [hw 2, hw 6]
      exact hgmuJ3
    have hwmuK0 : w 6 + w 9 = alpha + gamma := by
      rw [hw 6, hw 9]
      exact hgmuK0
    have hwmuK3 : w 0 + w 3 = alpha + gamma := by
      rw [hw 0, hw 3]
      exact hgmuK3
    have hnorm := mme_stothers_phi233_integer_histogram_normalization
      N alpha beta gamma hN w hwtotal hwsigma0 hwsigma2
        hwmuJ0 hwmuJ3 hwmuK0 hwmuK3
    dsimp only at hnorm
    obtain ⟨hpNonneg, hpTotal, hpSigma0, hpSigma2,
      hpMuJ0, hpMuJ3, hpMuK0, hpMuK3⟩ := hnorm
    rw [hsigmaRatio] at hpSigma0 hpSigma2
    rw [hmuRatio] at hpMuJ0 hpMuJ3 hpMuK0 hpMuK3
    have hpEntropy := hmax
      (fun r ↦ (w r : ℝ) / ((2 * N : ℕ) : ℝ))
      hpNonneg hpTotal hpSigma0 hpSigma2
      hpMuJ0 hpMuJ3 hpMuK0 hpMuK3
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbits := div_le_div_of_nonneg_right hpEntropy (le_of_lt hlog)
    simpa only [mme_modern_entropyBits, w, T] using hbits
  have hbound := mme_finite_word_family_histogram_entropy_upper
    (2 * N) (by omega) F (T / Real.log 2) hEntropy
  have hlogNe : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hexponent :
      (((2 * N : ℕ) : ℝ) * Real.log 2 * (T / Real.log 2)) =
        ((2 * N : ℕ) : ℝ) * T := by
    field_simp [hlogNe]
  rw [hexponent] at hbound
  rw [← hFcard]
  simpa only [Fintype.card_fin, T] using hbound


open MME Filter

set_option autoImplicit false

/-- Along any sequence of integral profiles converging to a positive
stationary `phi_233` profile, a compatible stationary completion profile
makes the ambient family larger than the exact family by only the explicit
polynomial factors and an arbitrarily small exponential loss. -/
theorem phi233_rounded_completion_ratio_general
    (N A B C D : ℕ → ℕ) (X Y Z W : ℕ → ℝ)
    (a b c d : ℝ)
    (hN : ∀ n, 0 < N n)
    (hsum : ∀ n, 2 * A n + B n + C n + D n = N n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hA : Tendsto (fun n ↦ (A n : ℝ) / (N n : ℝ)) atTop (nhds a))
    (hB : Tendsto (fun n ↦ (B n : ℝ) / (N n : ℝ)) atTop (nhds b))
    (hC : Tendsto (fun n ↦ (C n : ℝ) / (N n : ℝ)) atTop (nhds c))
    (hD : Tendsto (fun n ↦ (D n : ℝ) / (N n : ℝ)) atTop (nhds d))
    (hX : ∀ n, 0 < X n) (hY : ∀ n, 0 < Y n)
    (hZ : ∀ n, 0 < Z n) (hW : ∀ n, 0 < W n)
    (htotalX : ∀ n, 2 * X n + Y n + Z n + W n = 1)
    (hsigmaX : ∀ n,
      2 * X n + Y n =
        2 * ((A n : ℝ) / (N n : ℝ)) + (B n : ℝ) / (N n : ℝ))
    (hmuX : ∀ n,
      X n + Z n = (A n : ℝ) / (N n : ℝ) + (C n : ℝ) / (N n : ℝ))
    (hcritical : ∀ n,
      (X n) ^ (2 : ℕ) * W n = (Y n) ^ (2 : ℕ) * Z n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (Nat.card
            (MME.StothersFourth.Phi233.MarginalAddress
              (N n) (A n) (B n) (C n) (D n)) : ℝ) ≤
          (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
            Real.exp (((2 * N n : ℕ) : ℝ) * ε) *
            (6 * (((2 * N n + 1 : ℕ) : ℝ))) ^ 10 *
            (Nat.card
              (MME.StothersFourth.Phi233.ExactProfileAddress
                (N n) (A n) (B n) (C n) (D n)) : ℝ) := by
  let Ar : ℕ → ℝ := fun n ↦ (A n : ℝ) / (N n : ℝ)
  let Br : ℕ → ℝ := fun n ↦ (B n : ℝ) / (N n : ℝ)
  let Cr : ℕ → ℝ := fun n ↦ (C n : ℝ) / (N n : ℝ)
  let Dr : ℕ → ℝ := fun n ↦ (D n : ℝ) / (N n : ℝ)
  have hUniform := mme_stothers_phi233_uniform_entropy_stability
    a b c d Ar Br Cr Dr X Y Z W ha hb hc hd htotal hstation
    (by simpa only [Ar] using hA)
    (by simpa only [Br] using hB)
    (by simpa only [Cr] using hC)
    (by simpa only [Dr] using hD)
    (fun n ↦ (hX n).le) (fun n ↦ (hY n).le)
    (fun n ↦ (hZ n).le) (fun n ↦ (hW n).le) htotalX
    (by simpa only [Ar, Br] using hsigmaX)
    (by simpa only [Ar, Cr] using hmuX)
  intro ε hε
  filter_upwards [hUniform ε hε] with n hentropy
  have hsigmaCast :
      (((2 * A n + B n : ℕ) : ℝ) / (N n : ℝ)) =
        2 * Ar n + Br n := by
    dsimp only [Ar, Br]
    push_cast
    ring
  have hmuCast :
      (((A n + C n : ℕ) : ℝ) / (N n : ℝ)) =
        Ar n + Cr n := by
    dsimp only [Ar, Cr]
    push_cast
    ring
  have hstationX :=
    mme_stothers_phi233_log_stationarity_of_critical_product
      (X n) (Y n) (Z n) (W n) (hX n) (hY n) (hZ n) (hW n)
      (hcritical n)
  have hAmbient :=
    phi233_marginal_entropy_upper_general
      (N n) (A n) (B n) (C n) (D n) (hN n)
      (2 * Ar n + Br n) (Ar n + Cr n)
      (X n) (Y n) (Z n) (W n)
      hsigmaCast hmuCast (hX n) (hY n) (hZ n) (hW n)
      (htotalX n) (by simpa only [Ar, Br] using hsigmaX n)
      (by simpa only [Ar, Cr] using hmuX n) hstationX
  have hExact :=
    mme_stothers_phi233_exact_profile_entropy_polynomial_lower
      (N n) (A n) (B n) (C n) (D n) (hN n) (hsum n)
  let targetEntropy : ℝ :=
    4 * Real.negMulLog (Ar n / 2) +
      2 * Real.negMulLog (Br n / 2) +
      2 * Real.negMulLog (Cr n / 2) +
      2 * Real.negMulLog (Dr n / 2)
  let exactEntropy : ℝ :=
    4 * Real.negMulLog ((A n : ℝ) / ((2 * N n : ℕ) : ℝ)) +
      2 * Real.negMulLog ((B n : ℝ) / ((2 * N n : ℕ) : ℝ)) +
      2 * Real.negMulLog ((C n : ℝ) / ((2 * N n : ℕ) : ℝ)) +
      2 * Real.negMulLog ((D n : ℝ) / ((2 * N n : ℕ) : ℝ))
  have hAhalf : Ar n / 2 =
      (A n : ℝ) / ((2 * N n : ℕ) : ℝ) := by
    dsimp only [Ar]
    push_cast
    ring
  have hBhalf : Br n / 2 =
      (B n : ℝ) / ((2 * N n : ℕ) : ℝ) := by
    dsimp only [Br]
    push_cast
    ring
  have hChalf : Cr n / 2 =
      (C n : ℝ) / ((2 * N n : ℕ) : ℝ) := by
    dsimp only [Cr]
    push_cast
    ring
  have hDhalf : Dr n / 2 =
      (D n : ℝ) / ((2 * N n : ℕ) : ℝ) := by
    dsimp only [Dr]
    push_cast
    ring
  have hEntropyEq : targetEntropy = exactEntropy := by
    simp only [targetEntropy, exactEntropy, hAhalf, hBhalf, hChalf, hDhalf]
  have hentropy' :
      4 * Real.negMulLog (X n / 2) +
            2 * Real.negMulLog (Y n / 2) +
            2 * Real.negMulLog (Z n / 2) +
            2 * Real.negMulLog (W n / 2) ≤
        targetEntropy + ε := by
    simpa only [targetEntropy, Ar, Br, Cr, Dr] using hentropy
  have hexpMono :
      Real.exp (((2 * N n : ℕ) : ℝ) *
          (4 * Real.negMulLog (X n / 2) +
            2 * Real.negMulLog (Y n / 2) +
            2 * Real.negMulLog (Z n / 2) +
            2 * Real.negMulLog (W n / 2))) ≤
        Real.exp (((2 * N n : ℕ) : ℝ) * (targetEntropy + ε)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hentropy' (by positivity)
  have hExact' :
      Real.exp (((2 * N n : ℕ) : ℝ) * exactEntropy) ≤
        (6 * (((2 * N n + 1 : ℕ) : ℝ))) ^ 10 *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              (N n) (A n) (B n) (C n) (D n)) : ℝ) := by
    simpa only [exactEntropy] using hExact
  calc
    (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          (N n) (A n) (B n) (C n) (D n)) : ℝ) ≤
        (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N n : ℕ) : ℝ) *
            (4 * Real.negMulLog (X n / 2) +
              2 * Real.negMulLog (Y n / 2) +
              2 * Real.negMulLog (Z n / 2) +
              2 * Real.negMulLog (W n / 2))) := hAmbient
    _ ≤ (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N n : ℕ) : ℝ) * (targetEntropy + ε)) :=
      mul_le_mul_of_nonneg_left hexpMono (by positivity)
    _ = (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N n : ℕ) : ℝ) * ε) *
          Real.exp (((2 * N n : ℕ) : ℝ) * exactEntropy) := by
      rw [← hEntropyEq]
      rw [mul_add, Real.exp_add]
      ring
    _ ≤ (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N n : ℕ) : ℝ) * ε) *
          ((6 * (((2 * N n + 1 : ℕ) : ℝ))) ^ 10 *
            (Nat.card
              (MME.StothersFourth.Phi233.ExactProfileAddress
                (N n) (A n) (B n) (C n) (D n)) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hExact' (by positivity)
    _ = (((2 * N n + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N n : ℕ) : ℝ) * ε) *
          (6 * (((2 * N n + 1 : ℕ) : ℝ))) ^ 10 *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              (N n) (A n) (B n) (C n) (D n)) : ℝ) := by ring


open MME Filter

set_option autoImplicit false

/-- The stationary completion profiles needed in the asymptotic count can
be selected automatically after discarding a finite prefix of any rounded
positive stationary target sequence. -/
theorem phi233_rounded_tail_completion_general
    (A B C D : ℕ → ℕ) (a b c d : ℝ)
    (hsum : ∀ n, 2 * A n + B n + C n + D n = n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hA : Tendsto (fun n ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hB : Tendsto (fun n ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b))
    (hC : Tendsto (fun n ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c))
    (hD : Tendsto (fun n ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d)) :
    ∃ k : ℕ, 0 < k ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          (Nat.card
              (MME.StothersFourth.Phi233.MarginalAddress
                (n + k) (A (n + k)) (B (n + k))
                (C (n + k)) (D (n + k))) : ℝ) ≤
            (((2 * (n + k) + 1 : ℕ) : ℝ)) ^ 10 *
              Real.exp (((2 * (n + k) : ℕ) : ℝ) * ε) *
              (6 * (((2 * (n + k) + 1 : ℕ) : ℝ))) ^ 10 *
              (Nat.card
                (MME.StothersFourth.Phi233.ExactProfileAddress
                  (n + k) (A (n + k)) (B (n + k))
                  (C (n + k)) (D (n + k))) : ℝ) := by
  let Ar : ℕ → ℝ := fun n ↦ (A n : ℝ) / (n : ℝ)
  let Br : ℕ → ℝ := fun n ↦ (B n : ℝ) / (n : ℝ)
  let Cr : ℕ → ℝ := fun n ↦ (C n : ℝ) / (n : ℝ)
  let Dr : ℕ → ℝ := fun n ↦ (D n : ℝ) / (n : ℝ)
  let sigma : ℕ → ℝ := fun n ↦ 2 * Ar n + Br n
  let mu : ℕ → ℝ := fun n ↦ Ar n + Cr n
  have hAr : Tendsto Ar atTop (nhds a) := by simpa only [Ar] using hA
  have hBr : Tendsto Br atTop (nhds b) := by simpa only [Br] using hB
  have hCr : Tendsto Cr atTop (nhds c) := by simpa only [Cr] using hC
  have hDr : Tendsto Dr atTop (nhds d) := by simpa only [Dr] using hD
  have hSigma : Tendsto sigma atTop (nhds (2 * a + b)) := by
    simpa only [sigma] using (hAr.const_mul 2).add hBr
  have hMu : Tendsto mu atTop (nhds (a + c)) := by
    simpa only [mu] using hAr.add hCr
  have hCompat : Tendsto (fun n ↦ sigma n / 2 + mu n) atTop
      (nhds ((2 * a + b) / 2 + (a + c))) :=
    (hSigma.div_const 2).add hMu
  have hsigma0 : 0 < 2 * a + b := by linarith
  have hmu0 : 0 < a + c := by linarith
  have hcompatLimit : (2 * a + b) / 2 + (a + c) < 1 := by
    nlinarith
  have hsigmaUpper : 2 * a + b < 1 := by linarith
  have hgood : ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < sigma n ∧ sigma n < 1 ∧
        0 < mu n ∧ sigma n / 2 + mu n < 1 := by
    filter_upwards [eventually_gt_atTop 0,
      hSigma.eventually_const_lt hsigma0,
      hSigma.eventually_lt_const hsigmaUpper,
      hMu.eventually_const_lt hmu0,
      hCompat.eventually_lt_const hcompatLimit] with n hn hs0 hsU hm0 hcomp
    exact ⟨hn, hs0, hsU, hm0, hcomp⟩
  obtain ⟨k, hk⟩ := (eventually_atTop.1 hgood)
  have hshift (n : ℕ) :
      0 < n + k ∧ 0 < sigma (n + k) ∧ sigma (n + k) < 1 ∧
        0 < mu (n + k) ∧ sigma (n + k) / 2 + mu (n + k) < 1 := by
    exact hk (n + k) (by omega)
  let sigmaShift : ℕ → ℝ := fun n ↦ sigma (n + k)
  let muShift : ℕ → ℝ := fun n ↦ mu (n + k)
  obtain ⟨X, Y, Z, W, hX, hY, hZ, hW, htotalX, hsigmaX, hmuX,
      hcritical⟩ :=
    mme_stothers_phi233_stationary_profile_sequence_exists
      sigmaShift muShift
      (fun n ↦ by simpa only [sigmaShift] using (hshift n).2.1)
      (fun n ↦ by simpa only [muShift] using (hshift n).2.2.2.1)
      (fun n ↦ by
        have h := (hshift n).2.2.1
        dsimp only [sigmaShift]
        linarith)
      (fun n ↦ by
        simpa only [sigmaShift, muShift] using (hshift n).2.2.2.2)
  have hRatio :=
    phi233_rounded_completion_ratio_general
      (fun n ↦ n + k) (fun n ↦ A (n + k)) (fun n ↦ B (n + k))
      (fun n ↦ C (n + k)) (fun n ↦ D (n + k)) X Y Z W a b c d
      (fun n ↦ (hshift n).1)
      (fun n ↦ hsum (n + k)) ha hb hc hd htotal hstation
      (by simpa only [Ar] using hAr.comp (tendsto_add_atTop_nat k))
      (by simpa only [Br] using hBr.comp (tendsto_add_atTop_nat k))
      (by simpa only [Cr] using hCr.comp (tendsto_add_atTop_nat k))
      (by simpa only [Dr] using hDr.comp (tendsto_add_atTop_nat k))
      hX hY hZ hW htotalX
      (by simpa only [sigmaShift, sigma, Ar, Br] using hsigmaX)
      (by simpa only [muShift, mu, Ar, Cr] using hmuX)
      hcritical
  exact ⟨k, (hk k (by omega)).1, hRatio⟩


open MME Filter

set_option autoImplicit false

/-- End-to-end analytic bridge for the exceptional `phi_233` count: every
positive stationary real profile has exact integral approximants whose
same-marginal ambiguity is subexponential. -/
theorem solution
    (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    :
    ∃ A B C D : ℕ → ℕ, ∃ k : ℕ,
      (∀ n, 2 * A n + B n + C n + D n = n) ∧
      Tendsto (fun n ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a) ∧
      Tendsto (fun n ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b) ∧
      Tendsto (fun n ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c) ∧
      Tendsto (fun n ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d) ∧
      0 < k ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          (Nat.card
              (MME.StothersFourth.Phi233.MarginalAddress
                (n + k) (A (n + k)) (B (n + k))
                (C (n + k)) (D (n + k))) : ℝ) ≤
            (((2 * (n + k) + 1 : ℕ) : ℝ)) ^ 10 *
              Real.exp (((2 * (n + k) : ℕ) : ℝ) * ε) *
              (6 * (((2 * (n + k) + 1 : ℕ) : ℝ))) ^ 10 *
              (Nat.card
                (MME.StothersFourth.Phi233.ExactProfileAddress
                  (n + k) (A (n + k)) (B (n + k))
                  (C (n + k)) (D (n + k))) : ℝ) := by
  obtain ⟨A, B, C, D, hsum, hA, hB, hC, hD⟩ :=
    mme_stothers_phi233_exact_integer_profile_rounding
      a b c d ha.le hb.le hc.le hd.le htotal
  obtain ⟨k, hk, hratio⟩ :=
    phi233_rounded_tail_completion_general
      A B C D a b c d hsum ha hb hc hd htotal hstation
      hA hB hC hD
  exact ⟨A, B, C, D, k, hsum, hA, hB, hC, hD, hk, hratio⟩
