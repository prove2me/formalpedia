-- Prove2me | solution 1 for FedAvg.TunedConvexFedAvgConvergence
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-23T03:22:04.851896+00:00
-- url     : https://prove2.me/submissions/ffb06882-5a79-4d97-9a6b-5579c8d2f7b3

import Definitions.Def_FedAvg_Model
import Theorems.Thm_FedAvg_ConvexFedAvgConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Wang et al., arXiv:2107.06917v1, Section 6.1.2, PDF p. 41, equations (16)--(17).
The scalar tuning argument is proved here; the stochastic reduction depends on the
published constant-step root, equation (15). -/

open MeasureTheory

namespace FedAvg

lemma optimizedStep_pos {d M τ T : ℕ} (P : Problem d M)
    (hτ : 0 < τ) (hT : 0 < T) (hD : 0 < distance P)
    (hσ : 0 < P.σ) (hζ : 0 < P.ζ) : 0 < optimizedStep P τ T := by
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr P.clients_pos
  have hτ' : (0 : ℝ) < τ := Nat.cast_pos.mpr hτ
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hL := P.smoothness_pos
  unfold optimizedStep
  simp only [Real.rpow_eq_pow]
  positivity

lemma optimizedStep_le {d M τ T : ℕ} (P : Problem d M) :
    optimizedStep P τ T ≤ 1 / (4 * P.L) := min_le_left _ _

private lemma rpow_third_mul (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.rpow x ((n : ℝ) / 3) = (Real.rpow x (1 / 3 : ℝ)) ^ n := by
  simp only [Real.rpow_eq_pow]
  rw [show (n : ℝ) / 3 = (1 / 3 : ℝ) * n by ring,
    Real.rpow_mul_natCast hx]

private lemma third_pow_three (x : ℝ) (hx : 0 ≤ x) :
    (Real.rpow x (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← rpow_third_mul x hx 3]
  norm_num

private lemma rpow_two_thirds (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (2 / 3 : ℝ) = (Real.rpow x (1 / 3 : ℝ)) ^ 2 := by
  simpa using rpow_third_mul x hx 2

private lemma rpow_four_thirds (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (4 / 3 : ℝ) = (Real.rpow x (1 / 3 : ℝ)) ^ 4 := by
  simpa using rpow_third_mul x hx 4

private lemma four_step_bound (a b c e k u v w A B C E : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hka : k / a ≤ A) (hkb : k / b ≤ B) (hkc : k / c ≤ C) (hke : k / e ≤ E)
    (hub : u * b ≤ B) (hvc : v * c ^ 2 ≤ C) (hwe : w * e ^ 2 ≤ E) :
    let η := min a (min b (min c e))
    k / η + u * η + 4 * v * η ^ 2 + 18 * w * η ^ 2 ≤
      A + 2 * B + 5 * C + 19 * E := by
  dsimp
  let η := min a (min b (min c e))
  have hη : 0 < η := lt_min ha (lt_min hb (lt_min hc he))
  have hηb : η ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hηc : η ≤ c := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hηe : η ≤ e := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hk : k / η ≤ A + B + C + E := by
    rcases min_choice a (min b (min c e)) with h | h
    · change k / min a (min b (min c e)) ≤ _
      rw [h]
      linarith
    · rcases min_choice b (min c e) with h' | h'
      · change k / min a (min b (min c e)) ≤ _
        rw [h, h']
        linarith
      · rcases min_choice c e with h'' | h''
        · change k / min a (min b (min c e)) ≤ _
          rw [h, h', h'']
          linarith
        · change k / min a (min b (min c e)) ≤ _
          rw [h, h', h'']
          linarith
  have huη : u * η ≤ B := (mul_le_mul_of_nonneg_left hηb hu).trans hub
  have hvη : v * η ^ 2 ≤ C :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hηc 2) hv).trans hvc
  have hwη : w * η ^ 2 ≤ E :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hηe 2) hw).trans hwe
  change k / η + u * η + 4 * v * η ^ 2 + 18 * w * η ^ 2 ≤ _
  nlinarith

lemma convergenceRHS_optimized_le {d M τ T : ℕ} (P : Problem d M)
    (hτ : 0 < τ) (hT : 0 < T) (hD : 0 < distance P)
    (hσ : 0 < P.σ) (hζ : 0 < P.ζ) :
    convergenceRHS P τ T (optimizedStep P τ T) ≤ optimizedRHS P τ T := by
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr P.clients_pos
  have hτ' : (0 : ℝ) < τ := Nat.cast_pos.mpr hτ
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hL := P.smoothness_pos
  let m := Real.sqrt (M : ℝ)
  let nt := Real.sqrt (τ : ℝ)
  let nr := Real.sqrt (T : ℝ)
  let q := Real.rpow (distance P) (1 / 3 : ℝ)
  let t := Real.rpow (τ : ℝ) (1 / 3 : ℝ)
  let r := Real.rpow (T : ℝ) (1 / 3 : ℝ)
  let l := Real.rpow P.L (1 / 3 : ℝ)
  let s := Real.rpow P.σ (1 / 3 : ℝ)
  let z := Real.rpow P.ζ (1 / 3 : ℝ)
  have hm : 0 < m := Real.sqrt_pos.mpr hM
  have hnt : 0 < nt := Real.sqrt_pos.mpr hτ'
  have hnr : 0 < nr := Real.sqrt_pos.mpr hT'
  have hq : 0 < q := Real.rpow_pos_of_pos hD _
  have ht : 0 < t := Real.rpow_pos_of_pos hτ' _
  have hr : 0 < r := Real.rpow_pos_of_pos hT' _
  have hl : 0 < l := Real.rpow_pos_of_pos hL _
  have hs : 0 < s := Real.rpow_pos_of_pos hσ _
  have hz : 0 < z := Real.rpow_pos_of_pos hζ _
  have hm2 : m ^ 2 = (M : ℝ) := Real.sq_sqrt hM.le
  have hnt2 : nt ^ 2 = (τ : ℝ) := Real.sq_sqrt hτ'.le
  have hnr2 : nr ^ 2 = (T : ℝ) := Real.sq_sqrt hT'.le
  have hq3 : q ^ 3 = distance P := third_pow_three _ hD.le
  have ht3 : t ^ 3 = (τ : ℝ) := third_pow_three _ hτ'.le
  have hr3 : r ^ 3 = (T : ℝ) := third_pow_three _ hT'.le
  have hl3 : l ^ 3 = P.L := third_pow_three _ hL.le
  have hs3 : s ^ 3 = P.σ := third_pow_three _ hσ.le
  have hz3 : z ^ 3 = P.ζ := third_pow_three _ hζ.le
  have hsqrt : Real.sqrt ((M : ℝ) * (τ : ℝ) * (T : ℝ)) = m * nt * nr := by
    rw [Real.sqrt_mul (mul_nonneg hM.le hτ'.le), Real.sqrt_mul hM.le]
  let a := 1 / (4 * P.L)
  let b := m * distance P / (nt * nr * P.σ)
  let c := q ^ 2 / (t ^ 2 * r * l * s ^ 2)
  let e := q ^ 2 / ((τ : ℝ) * r * l * z ^ 2)
  let k := distance P ^ 2 / (2 * (τ : ℝ) * (T : ℝ))
  let u := P.σ ^ 2 / (M : ℝ)
  let v := (τ : ℝ) * P.L * P.σ ^ 2
  let w := (τ : ℝ) ^ 2 * P.L * P.ζ ^ 2
  let A := 2 * P.L * distance P ^ 2 / ((τ : ℝ) * (T : ℝ))
  let B := P.σ * distance P / (m * nt * nr)
  let C := l * s ^ 2 * q ^ 4 / (t * r ^ 2)
  let E := l * z ^ 2 * q ^ 4 / r ^ 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have he : 0 < e := by dsimp only [e]; positivity
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hka : k / a = A := by
    dsimp only [k, a, A]
    field_simp
    ring
  have hkb : k / b = B / 2 := by
    dsimp only [k, b, B]
    rw [← hnt2, ← hnr2]
    field_simp
  have hub : u * b = B := by
    dsimp only [u, b, B]
    rw [← hm2]
    field_simp
  have hkc : k / c = C / 2 := by
    dsimp only [k, c, C]
    rw [← hq3, ← ht3, ← hr3]
    field_simp
  have hvc : v * c ^ 2 = C := by
    dsimp only [v, c, C]
    rw [← ht3, ← hl3, ← hs3]
    field_simp
  have hke : k / e = E / 2 := by
    dsimp only [k, e, E]
    rw [← hq3, ← hr3]
    field_simp
  have hwe : w * e ^ 2 = E := by
    dsimp only [w, e, E]
    rw [← hl3, ← hz3]
    field_simp
  have hstep : optimizedStep P τ T = min a (min b (min c e)) := by
    dsimp only [optimizedStep, a, b, c, e, m, nt, nr, q, t, r, l, s, z]
    rw [rpow_two_thirds _ hD.le, rpow_two_thirds _ hτ'.le,
      rpow_two_thirds _ hσ.le, rpow_two_thirds _ hζ.le]
  have hright : optimizedRHS P τ T = A + 2 * B + 5 * C + 19 * E := by
    unfold optimizedRHS
    rw [hsqrt]
    dsimp only [A, B, C, E, q, t, r, l, s, z]
    rw [rpow_four_thirds _ hD.le, rpow_two_thirds _ hσ.le,
      rpow_two_thirds _ hζ.le, rpow_two_thirds _ hT'.le]
    ring
  have hη := optimizedStep_pos P hτ hT hD hσ hζ
  have hleft : convergenceRHS P τ T (optimizedStep P τ T) =
      k / optimizedStep P τ T + u * optimizedStep P τ T +
        4 * v * optimizedStep P τ T ^ 2 + 18 * w * optimizedStep P τ T ^ 2 := by
    dsimp only [convergenceRHS, k, u, v, w]
    field_simp
  rw [hleft, hright, hstep]
  exact four_step_bound a b c e k u v w A B C E ha hb hc he hu hv hw hA hB hC hE
    hka.le (by linarith) (by linarith) (by linarith) hub.le hvc.le hwe.le

lemma tuned_of_constant_bound {d M τ T : ℕ} (P : Problem d M)
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hτ : 0 < τ) (hT : 0 < T) (hD : 0 < distance P)
    (hσ : 0 < P.σ) (hζ : 0 < P.ζ)
    (hconstant : ∀ η : ℝ, 0 < η → η ≤ 1 / (4 * P.L) →
      ∀ R : Run P μ τ T η, (∫ ω, avgLoss R ω ∂μ) ≤ convergenceRHS P τ T η)
    (R : Run P μ τ T (optimizedStep P τ T)) :
    (∫ ω, avgLoss R ω ∂μ) ≤ optimizedRHS P τ T := by
  exact (hconstant (optimizedStep P τ T) (optimizedStep_pos P hτ hT hD hσ hζ)
    (optimizedStep_le P) R).trans (convergenceRHS_optimized_le P hτ hT hD hσ hζ)

end FedAvg

open FedAvg
universe u

theorem solution :
    ∀ (d M : ℕ) (P : Problem d M) (Ω : Type u) [MeasurableSpace Ω]
      [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (τ T : ℕ),
      0 < τ → 0 < T → 0 < distance P → 0 < P.σ → 0 < P.ζ →
      ∀ R : Run P μ τ T (optimizedStep P τ T),
        (∫ ω, avgLoss R ω ∂μ) ≤ optimizedRHS P τ T := by
  intro d M P Ω _ _ μ _ τ T hτ hT hD hσ hζ R
  apply tuned_of_constant_bound P μ hτ hT hD hσ hζ ?_ R
  intro η hη hηmax R'
  exact FedAvg.ConvexFedAvgConvergence d M P Ω μ τ T η hτ hT hη hηmax R'

