-- Prove2me | solution 1 for mme_stothers_phi134_weighted_isolated_profile_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:47:01.348056+00:00
-- url     : https://prove2.me/submissions/09286b16-2860-491c-bcef-9fd75b0a5c05

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi134_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi134_capacity_identity
import Theorems.Thm_mme_stothers_phi134_cyclic_degree_bounds
import Theorems.Thm_mme_stothers_phi134_behrend_prime_of_cyclic_degree
import Theorems.Thm_mme_stothers_phi134_profile_weight_surplus_over_degree
import Theorems.Thm_mme_stothers_phi134_finite_isolation_of_hash_margin

open MME Real BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option warningAsError true

/-- The analytic Phi134 surplus, the prime--Behrend labels, and sharp Type-2
isolation combine into a single weighted exact-profile family. -/
theorem solution
    (sigma a c L E H V : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (hV : 0 ≤ V)
    (hVlt :
      V <
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) :
    ∃ N alpha beta gamma delta : ℕ,
      0 < N ∧ alpha + beta + gamma + delta = N ∧
      ∃ kept : Finset (CyclicExactEdge N alpha beta gamma delta),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
        (∀ x y z : kept,
          CyclicCoordinatewiseSupported x.1 y.1 z.1 →
            x = y ∧ y = z) ∧
        V ^ (2 * N) <
          (kept.card : ℝ) *
            (L ^ (2 * beta + 2 * gamma) *
              E ^ (2 * alpha + 2 * beta + 4 * delta) *
              H ^ (2 * gamma)) := by
  classical
  obtain ⟨N, alpha, beta, gamma, delta, hN, hsum, hsurplus⟩ :=
    mme_stothers_phi134_profile_weight_surplus_over_degree
      sigma a c L E H V ha hc hcs hsa hL hE hH hV hVlt
  let d : Fin 3 → ℕ := fun t ↦
    ∏ s : Fin 5,
      (marginalMultiplicity N alpha beta gamma delta t s).factorial /
        ∏ r : {r : Fin 8 // pattern r t = s},
          (profileMultiplicity alpha beta gamma delta r.1).factorial
  let D : ℕ := d 0 * (d 1 * d 2)
  let A : ℕ := ∏ i : Fin 3,
    Nat.multinomial Finset.univ
      (marginalMultiplicity N alpha beta gamma delta i)
  let C : ℝ :=
    (Nat.card (ExactProfileAddress N alpha beta gamma delta) : ℝ) ^ (3 : ℕ)
  let F : ℝ := Real.exp (2000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ))
  let B : ℝ :=
    L ^ (2 * beta + 2 * gamma) *
      E ^ (2 * alpha + 2 * beta + 4 * delta) *
      H ^ (2 * gamma)
  change V ^ (2 * N) * (D : ℝ) *
      Real.exp (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) < C * B at hsurplus
  have hDbounds :=
    mme_stothers_phi134_cyclic_degree_bounds
      N alpha beta gamma delta hsum
  change 1 ≤ D ∧ D ≤ 5 ^ (12 * N) at hDbounds
  have hD : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D by omega)
  have hF : 0 < F := by
    dsimp [F]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  obtain ⟨p, hp, hp7, S, hfree, hlarge, hpbound⟩ :=
    mme_stothers_phi134_behrend_prime_of_cyclic_degree
      N alpha beta gamma delta hsum
  have hlarge' : 6 * (D : ℝ) ≤ (S.card : ℝ) := by
    simpa only [D, d, Nat.cast_mul] using hlarge
  have hpbound' : (p : ℝ) ≤ (D : ℝ) * F := by
    simpa only [D, d, F, Nat.cast_mul] using hpbound
  letI : Fact p.Prime := ⟨hp⟩
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  let loss : ℝ :=
    (D : ℝ) * ((S.card : ℝ) / (2 * (p : ℝ) ^ 2))
  have hcancel :
      ((p ^ 2 : ℕ) : ℝ) * loss =
        (D : ℝ) * (S.card : ℝ) / 2 := by
    dsimp [loss]
    push_cast
    field_simp
  have hmargin :
      ((p ^ 2 : ℕ) : ℝ) * loss +
          3 * (D : ℝ) * (D : ℝ) ≤
        (D : ℝ) * (S.card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlarge' hD.le
    rw [hcancel]
    nlinarith
  obtain ⟨q, kept, hkept, hinj, hdiag, hretained⟩ :=
    (mme_stothers_phi134_finite_isolation_of_hash_margin
      hp7 hsum S hfree loss) (by
        simpa only [D, d, Nat.cast_mul] using hmargin)
  have hcapacity :=
    mme_stothers_phi134_capacity_identity
      N alpha beta gamma delta hsum
  change A * D =
    (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 at hcapacity
  have hcapacityR : (A : ℝ) * (D : ℝ) = C := by
    dsimp [C]
    exact_mod_cast hcapacity
  have hcount :
      C * ((S.card : ℝ) / (2 * (p : ℝ) ^ 2)) ≤
        (kept.card : ℝ) := by
    calc
      C * ((S.card : ℝ) / (2 * (p : ℝ) ^ 2)) =
          (A : ℝ) * loss := by
            rw [← hcapacityR]
            dsimp [loss]
            ring
      _ ≤ (kept.card : ℝ) := hretained
  have hFsq :
      F ^ 2 =
        Real.exp (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) := by
    dsimp [F]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hbudget : V ^ (2 * N) * (D : ℝ) * F ^ 2 < C * B := by
    rw [hFsq]
    exact hsurplus
  have hpden : 0 < 2 * (p : ℝ) ^ 2 := by positivity
  have hcount' :
      C * (S.card : ℝ) ≤
        (kept.card : ℝ) * (2 * (p : ℝ) ^ 2) := by
    apply (div_le_iff₀ hpden).mp
    simpa only [mul_div_assoc] using hcount
  have hleft :
      6 * (D : ℝ) * C ≤
        (kept.card : ℝ) * (2 * (p : ℝ) ^ 2) := by
    have hlabelsC := mul_le_mul_of_nonneg_left hlarge' (by positivity : 0 ≤ C)
    nlinarith
  have hpSq : (p : ℝ) ^ 2 ≤ ((D : ℝ) * F) ^ 2 :=
    pow_le_pow_left₀ hpR.le hpbound' 2
  have hright :
      (kept.card : ℝ) * (2 * (p : ℝ) ^ 2) ≤
        (kept.card : ℝ) * (2 * ((D : ℝ) * F) ^ 2) := by
    gcongr
  have hboth := hleft.trans hright
  have hratio : C ≤ (kept.card : ℝ) * ((D : ℝ) * F ^ 2) := by
    nlinarith [mul_pos hD hF]
  have hweighted := mul_le_mul_of_nonneg_right hratio hB.le
  have hscale : 0 < (D : ℝ) * F ^ 2 := by positivity
  have hfinal : V ^ (2 * N) < (kept.card : ℝ) * B := by
    apply (mul_lt_mul_iff_left₀ hscale).mp
    nlinarith
  exact ⟨N, alpha, beta, gamma, delta, hN, hsum,
    kept, hinj, hdiag, hfinal⟩
