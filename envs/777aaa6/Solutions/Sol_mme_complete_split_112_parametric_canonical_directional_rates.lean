-- Prove2me | solution 1 for mme_complete_split_112_parametric_canonical_directional_rates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:34:08.580324+00:00
-- url     : https://prove2.me/submissions/332219c4-b83b-41cb-be16-9af22e726d1b

import Theorems.Thm_mme_complete_split_112_parametric_profile_canonical_stars
import Theorems.Thm_mme_complete_split_112_positive_profile_cofinal_families
import Theorems.Thm_mme_complete_split_112_zero_profile_family
import Theorems.Thm_mme_complete_split_112_outer_star_entropy_rate
import Theorems.Thm_mme_central_binomial_sqrt_loss_log_rate
import Mathlib.Tactic

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem all_profile_cofinal_families
    (l g : ℕ) (hbalance : 341 * l < 100 * g) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N : ℕ := (l + g) * m
        let L : ℕ := l * m
        let G : ℕ := g * m
        let Zcount : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
          0 < A ∧ H ≤ 4 ^ N ∧
          (Zcount : ℝ) * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            (A : ℝ) ∧
          (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) := by
  by_cases hl : l = 0
  · subst l
    refine ⟨0, le_rfl, Eventually.of_forall ?_⟩
    intro m
    dsimp only
    simp only [zero_add, zero_mul]
    obtain ⟨⟨family⟩, hH⟩ := mme_complete_split_112_zero_profile_family (g * m)
    refine ⟨1, Nat.choose (2 * (g * m)) (g * m),
      (by simpa only [zero_add, zero_mul] using family), by decide, hH, ?_, ?_⟩
    · simp
    · simp only [mul_zero, zero_mul, Real.exp_zero, mul_one,
        Nat.cast_one]
      nlinarith only [Nat.cast_nonneg (α := ℝ) (Nat.choose (2 * (g * m)) (g * m))]
  · exact mme_complete_split_112_positive_profile_cofinal_families
      l g (Nat.pos_of_ne_zero hl) hbalance

private theorem parametric_z_entropy (p : ℚ) :
    mme_modern_entropyBits
        (fun sigma : Fin 2 → Fin 3 => (profileProbability p 2 sigma : ℝ)) =
      mme_modern_entropyBits ![(p : ℝ), (p : ℝ), 1 - 2 * (p : ℝ)] := by
  classical
  unfold mme_modern_entropyBits
  congr 1
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 3)
    (fun sigma => Real.negMulLog (profileProbability p 2 sigma : ℝ))
    (fun pair => Real.negMulLog (profileProbability p 2 ![pair.1, pair.2] : ℝ))
    (by intro sigma; rfl)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ, profileProbability, add_comm]

/-- Rates of the exact MM dimensions already exposed in the conclusion. -/
private theorem parametric_side_rates (l g m : ℕ) (hD : 0 < l + g) (hm : 0 < m) :
    Real.log ((5 ^ (2 * (g * m)) : ℕ) : ℝ) /
        ((2 * ((l + g) * m) : ℕ) : ℝ) =
      (g : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 ∧
    Real.log ((5 ^ (2 * (l * m)) : ℕ) : ℝ) /
        ((2 * ((l + g) * m) : ℕ) : ℝ) =
      (l : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hD0 : (l : ℝ) + (g : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  constructor <;> push_cast <;> rw [Real.log_pow] <;>
    push_cast <;> field_simp

/-- Every unrotated rational112 profile in the established hashing range,
including zero, has the same-family canonical directional rate package. -/
theorem solution (l g : ℕ) (hbalance : 341 * l < 100 * g) :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (profileProbability ((l : ℚ) / (2 * ((l + g : ℕ) : ℚ))) mode sigma : ℝ)) ∧
      ∀ delta : ℝ, 0 < delta →
        ∀ᶠ m : ℕ in atTop,
          let N : ℕ := (l + g) * m
          let L : ℕ := l * m
          let G : ℕ := g * m
          ∃ A H : ℕ, ∃ family : CWQ6PrimaryHashFamily N L G A H,
            0 < A ∧ H ≤ 4 ^ N ∧
            ((2 * N : ℕ) : ℝ) *
                (Real.log 2 * mme_modern_entropyBits (beta 2).probability - delta) ≤
              Real.log (A : ℝ) ∧
            ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
              Real.log ((A : ℝ) * (H : ℝ)) ∧
            Real.log ((5 ^ (2 * G) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) =
              (g : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 ∧
            Real.log ((5 ^ (2 * L) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) =
              (l : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 ∧
            ∀ (K : Type u) [Field K] (epsilon : ℝ≥0),
              TensorObj.Restrict
                (TensorObj.bigAdd (starObj (grading K 5) family))
                (restrictedCanonicalPower K 5 beta epsilon (2 * N)) ∧
              ∀ a : Fin A,
                (∀ sigma : Fin 3 → Fin (H + 1),
                  sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
                    (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
                ∀ h : Fin H,
                  TensorObj.Isomorphic
                    (MMObj K (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G)))
                    ((starGrading (grading K 5) family a).blockSubtensor
                      (cTensorOneHOneAddress H h)) := by
  have hD : 0 < l + g := by omega
  have hDq : (0 : ℚ) < ((l + g : ℕ) : ℚ) := by exact_mod_cast hD
  have hDq0 : (l : ℚ) + (g : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  let p : ℚ := (l : ℚ) / (2 * ((l + g : ℕ) : ℚ))
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp2 : 2 * p ≤ 1 := by
    have hle : p ≤ 1 / 2 := by
      dsimp [p]
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 * ((l + g : ℕ) : ℚ))).2
      have hlg : (l : ℚ) ≤ ((l + g : ℕ) : ℚ) := by exact_mod_cast Nat.le_add_right l g
      linarith
    linarith
  obtain ⟨beta, hbeta, _hsupport, hstars⟩ :=
    mme_complete_split_112_parametric_profile_canonical_stars.{u} p hp hp2
  obtain ⟨C, _hC, hfamilies⟩ := all_profile_cofinal_families l g hbalance
  have hpcast : (p : ℝ) = (l : ℝ) / (2 * ((l + g : ℕ) : ℝ)) := by
    simp only [p, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
  have hentropy :
      mme_modern_entropyBits (beta 2).probability =
        mme_modern_entropyBits
          ![(l : ℝ) / (2 * ((l + g : ℕ) : ℝ)),
            (l : ℝ) / (2 * ((l + g : ℕ) : ℝ)),
            1 - 2 * ((l : ℝ) / (2 * ((l + g : ℕ) : ℝ)))] := by
    rw [show (beta 2).probability =
      (fun sigma => (profileProbability p 2 sigma : ℝ)) from funext (hbeta 2)]
    simpa only [hpcast] using parametric_z_entropy p
  refine ⟨beta, hbeta, ?_⟩
  intro delta hdelta
  have he := mme_complete_split_112_outer_star_entropy_rate l g hD C delta hdelta
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (mme_central_binomial_sqrt_loss_log_rate C delta hdelta)
  filter_upwards [hfamilies, he, eventually_ge_atTop n₀, eventually_gt_atTop 0]
    with m hm hme hmn hmpos
  dsimp only at hm hme ⊢
  obtain ⟨A, H, family, hApos, hH, hA, hAH⟩ := hm
  have hAHpos : (0 : ℝ) < (A : ℝ) * (H : ℝ) := by
    exact_mod_cast Nat.mul_pos hApos family.hHpos
  have hNm : n₀ ≤ (l + g) * m := hmn.trans (Nat.le_mul_of_pos_left m hD)
  have hlogAH := hn₀ ((l + g) * m) hNm
    ((A : ℝ) * (H : ℝ)) hAHpos (by simpa only [mul_assoc] using hAH)
  have hlogA := hme (A : ℝ) (by exact_mod_cast hApos) hA
  obtain ⟨hsideG, hsideL⟩ := parametric_side_rates l g m hD hmpos
  refine ⟨A, H, family, hApos, hH, ?_, ?_, hsideG, hsideL, ?_⟩
  · simpa only [hentropy] using hlogA
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlogAH
  · intro K inst epsilon
    have hLG : l * m + g * m = (l + g) * m := by ring
    have hLp : ((l * m : ℕ) : ℚ) = (2 * ((l + g) * m) : ℕ) * p := by
      dsimp [p]
      push_cast
      field_simp
    exact hstars K 5 ((l + g) * m) (l * m) (g * m) A H family hLG hLp epsilon
