-- Prove2me | solution 1 for mme_stothers_phi134_analytic_profile_surplus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:45:08.74472+00:00
-- url     : https://prove2.me/submissions/d9f7fe45-ad8c-435b-bbe1-e3e0005d2590

import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi134_entropy_rate_identity

open MME Real BigOperators Filter

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace MME.StothersFourth.Phi134AnalyticSurplus

private theorem scaled_log_limit (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.log (s * n + 1) / (2 * n))
      atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ s * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  have hl := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ht
  have hr : Tendsto (fun n : ℕ ↦ (s * n + 1) / (2 * n))
      atTop (nhds (s / 2)) := by
    have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hh := ((tendsto_const_nhds (x := s)).add hi).div_const (2 : ℝ)
    convert hh.congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp
  have hh := hl.mul hr
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < s * (n : ℝ) + 1 := by positivity
    simp only [Function.comp_apply, pow_one, one_mul, add_zero]
    field_simp

private theorem scaled_sqrt_limit (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.sqrt (s * n + 1) / (2 * n))
      atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ s * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp ht)
  have hr : Tendsto (fun n : ℕ ↦ (s * n + 1) / (2 * n))
      atTop (nhds (s / 2)) := by
    have hin : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hh := ((tendsto_const_nhds (x := s)).add hin).div_const (2 : ℝ)
    convert hh.congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp
  have hh := hi.mul hr
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < s * (n : ℝ) + 1 := by positivity
    have hsqrt : Real.sqrt (s * n + 1) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    simp only [Function.comp_apply]
    field_simp
    nlinarith [Real.sq_sqrt hpos.le]

private theorem penalty_limit :
    Tendsto (fun n : ℕ ↦
      (15 * Real.log (6 * ((2 * n + 1 : ℕ) : ℝ)) +
        4000 * Real.sqrt ((12 * n + 1 : ℕ) : ℝ)) / (2 * n))
      atTop (nhds 0) := by
  have hl := scaled_log_limit 2 (by norm_num)
  have hs := scaled_sqrt_limit 12 (by norm_num)
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh :=
    ((((hi.const_mul (Real.log 6)).div_const 2).add hl).const_mul 15 |>.add
      (hs.const_mul 4000))
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hp : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hp]
    ring

private noncomputable def entropyAt
    (A B C : ℕ → ℕ) (n : ℕ) : ℝ :=
  let an := (A n : ℝ) / n
  let cn := (C n : ℝ) / n
  let sn := ((B n : ℝ) + C n) / n
  (3 - cn) * Real.log 2 +
    Real.negMulLog sn + Real.negMulLog (1 - sn) +
    Real.negMulLog an + Real.negMulLog cn +
    Real.negMulLog (1 - an - cn)

end MME.StothersFourth.Phi134AnalyticSurplus

open MME.StothersFourth.Phi134AnalyticSurplus

/-- Abstract analytic heart of the Phi134 profile extraction.  Any exact
finite counting layer satisfying the displayed capacity lower bound can be
combined with convergent integral profile sequences to produce a strict
finite surplus. -/
theorem solution
    (sigma a c L E H V : ℝ)
    (A B C D degree targetCard : ℕ → ℕ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (hV : 0 < V)
    (hVlt :
      V <
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c)))
    (hsum : ∀ n, A n + B n + C n + D n = n)
    (hA : Tendsto (fun n : ℕ ↦ (A n : ℝ) / n) atTop (nhds a))
    (hB : Tendsto (fun n : ℕ ↦ (B n : ℝ) / n) atTop
      (nhds (sigma - c)))
    (hC : Tendsto (fun n : ℕ ↦ (C n : ℝ) / n) atTop (nhds c))
    (hD : Tendsto (fun n : ℕ ↦ (D n : ℝ) / n) atTop
      (nhds (1 - sigma - a)))
    (hdegree : ∀ n, 0 < n → 0 < degree n)
    (hcapacity : ∀ n : ℕ, 0 < n →
      Real.exp ((2 * n : ℝ) *
        (let an := (A n : ℝ) / n
         let cn := (C n : ℝ) / n
         let sn := ((B n : ℝ) + C n) / n
         (3 - cn) * Real.log 2 +
           Real.negMulLog sn + Real.negMulLog (1 - sn) +
           Real.negMulLog an + Real.negMulLog cn +
           Real.negMulLog (1 - an - cn))) ≤
        (6 * ((2 * n + 1 : ℕ) : ℝ)) ^ (15 : ℕ) *
          ((targetCard n : ℝ) ^ (3 : ℕ) / (degree n : ℝ))) :
    ∃ n : ℕ, 0 < n ∧ A n + B n + C n + D n = n ∧
      V ^ (2 * n) * (degree n : ℝ) *
          Real.exp (4000 * Real.sqrt ((12 * n + 1 : ℕ) : ℝ)) <
        (targetCard n : ℝ) ^ (3 : ℕ) *
          (L ^ (2 * B n + 2 * C n) *
            E ^ (2 * A n + 2 * B n + 4 * D n) *
            H ^ (2 * C n)) := by
  let an := fun n : ℕ ↦ (A n : ℝ) / n
  let bn := fun n : ℕ ↦ (B n : ℝ) / n
  let cn := fun n : ℕ ↦ (C n : ℝ) / n
  let dn := fun n : ℕ ↦ (D n : ℝ) / n
  let sn := fun n : ℕ ↦ ((B n : ℝ) + C n) / n
  have hsn0 := hB.add hC
  have hsn : Tendsto sn atTop (nhds sigma) := by
    have hh : Tendsto sn atTop (nhds ((sigma - c) + c)) := by
      apply hsn0.congr'
      exact Filter.Eventually.of_forall (fun n ↦ by
        dsimp only [sn]
        rw [add_div])
    have hlimit : (sigma - c) + c = sigma := by ring
    rw [hlimit] at hh
    exact hh
  have hneg {f : ℕ → ℝ} {x : ℝ}
      (h : Tendsto f atTop (nhds x)) :
      Tendsto (fun n ↦ Real.negMulLog (f n)) atTop
        (nhds (Real.negMulLog x)) :=
    Real.continuous_negMulLog.continuousAt.tendsto.comp h
  have hthree : Tendsto (fun n ↦ (3 : ℝ) - cn n) atTop
      (nhds (3 - c)) := tendsto_const_nhds.sub hC
  have hones : Tendsto (fun n ↦ (1 : ℝ) - sn n) atTop
      (nhds (1 - sigma)) := tendsto_const_nhds.sub hsn
  have honeac : Tendsto (fun n ↦ (1 : ℝ) - an n - cn n) atTop
      (nhds (1 - a - c)) :=
    (tendsto_const_nhds.sub hA).sub hC
  have hent : Tendsto (fun n ↦ entropyAt A B C n) atTop
      (nhds
        ((3 - c) * Real.log 2 +
          Real.negMulLog sigma + Real.negMulLog (1 - sigma) +
          Real.negMulLog a + Real.negMulLog c +
          Real.negMulLog (1 - a - c))) := by
    have hh :=
      (((((hthree.mul_const (Real.log 2)).add (hneg hsn)).add
        (hneg hones)).add (hneg hA)).add (hneg hC)).add (hneg honeac)
    change Tendsto (fun n ↦
      (3 - cn n) * Real.log 2 +
        Real.negMulLog (sn n) + Real.negMulLog (1 - sn n) +
        Real.negMulLog (an n) + Real.negMulLog (cn n) +
        Real.negMulLog (1 - an n - cn n)) atTop _
    exact hh
  have hecoef0 := ((hA.add hB).add (hD.const_mul 2))
  have hecoef : Tendsto
      (fun n ↦ an n + bn n + 2 * dn n) atTop
      (nhds ((1 - sigma) + (1 - a - c))) := by
    change Tendsto (fun n ↦ an n + bn n + 2 * dn n) atTop _ at hecoef0
    have hlimit : a + (sigma - c) + 2 * (1 - sigma - a) =
        (1 - sigma) + (1 - a - c) := by ring
    rw [hlimit] at hecoef0
    exact hecoef0
  let rate := fun n : ℕ ↦ entropyAt A B C n +
    sn n * Real.log L +
    (an n + bn n + 2 * dn n) * Real.log E +
    cn n * Real.log H
  have hrate0 :=
    (((hent.add (hsn.mul_const (Real.log L))).add
      (hecoef.mul_const (Real.log E))).add
      (hC.mul_const (Real.log H)))
  have hrate : Tendsto rate atTop
      (nhds (Real.log
        (8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))))) := by
    rw [← mme_stothers_phi134_entropy_rate_identity
      sigma a c L E H ha hc hcs hsa hL hE hH]
    change Tendsto (fun n ↦ entropyAt A B C n +
      sn n * Real.log L +
      (an n + bn n + 2 * dn n) * Real.log E +
      cn n * Real.log H) atTop _
    exact hrate0
  have hlim := hrate.sub
    MME.StothersFourth.Phi134AnalyticSurplus.penalty_limit
  have hlog := Real.log_lt_log hV hVlt
  have hevent := hlim.eventually
    (eventually_gt_nhds (by simpa only [sub_zero] using hlog))
  obtain ⟨N, hN, hgap⟩ := ((eventually_gt_atTop 0).and hevent).exists
  let P : ℝ := 6 * ((2 * N + 1 : ℕ) : ℝ)
  let Q : ℝ := ((12 * N + 1 : ℕ) : ℝ)
  let Deg : ℝ := (degree N : ℝ)
  let T : ℝ := (targetCard N : ℝ) ^ (3 : ℕ)
  let J : ℝ :=
    L ^ (2 * B N + 2 * C N) *
      E ^ (2 * A N + 2 * B N + 4 * D N) *
      H ^ (2 * C N)
  have hDeg : 0 < Deg := by
    dsimp only [Deg]
    exact_mod_cast hdegree N hN
  have hP : 0 < P := by dsimp only [P]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hcap := hcapacity N hN
  change Real.exp ((2 * N : ℝ) * entropyAt A B C N) ≤
    P ^ (15 : ℕ) * (T / Deg) at hcap
  have hf := mul_le_mul_of_nonneg_right hcap hJ.le
  have hlogJ : Real.log J = (2 * N : ℝ) *
      (sn N * Real.log L +
        (an N + bn N + 2 * dn N) * Real.log E +
        cn N * Real.log H) := by
    dsimp only [J]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    dsimp only [sn, an, bn, cn, dn]
    field_simp
    ring
  have hleft :
      Real.exp ((2 * N : ℝ) * entropyAt A B C N) * J =
        Real.exp ((2 * N : ℝ) * rate N) := by
    rw [← Real.exp_log hJ, ← Real.exp_add, hlogJ]
    congr 1
    dsimp only [rate]
    ring
  rw [hleft] at hf
  have hngap :
      (2 * N : ℝ) * Real.log V + 15 * Real.log P +
          4000 * Real.sqrt Q <
        (2 * N : ℝ) * rate N := by
    have hh := mul_lt_mul_of_pos_left hgap
      (by positivity : (0 : ℝ) < 2 * N)
    change (2 * N : ℝ) * Real.log V <
      (2 * N : ℝ) *
        (rate N -
          (15 * Real.log P + 4000 * Real.sqrt Q) / (2 * N)) at hh
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    field_simp at hh
    nlinarith only [hh]
  have heq :
      (2 * N : ℝ) * Real.log V + 15 * Real.log P +
          4000 * Real.sqrt Q =
        Real.log
          (V ^ (2 * N) * P ^ (15 : ℕ) *
            Real.exp (4000 * Real.sqrt Q)) := by
    conv_rhs =>
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hh := (Real.exp_lt_exp.mpr hngap).trans_le hf
  rw [heq, Real.exp_log (by positivity)] at hh
  change
    V ^ (2 * N) * P ^ (15 : ℕ) *
        Real.exp (4000 * Real.sqrt Q) <
      P ^ (15 : ℕ) * (T / Deg) * J at hh
  have hcancel :
      V ^ (2 * N) * Real.exp (4000 * Real.sqrt Q) <
        (T / Deg) * J := by
    have hp15 : 0 < P ^ (15 : ℕ) := by positivity
    nlinarith only [hh, hp15]
  have hcancel' := mul_lt_mul_of_pos_right hcancel hDeg
  refine ⟨N, hN, hsum N, ?_⟩
  change V ^ (2 * N) * Deg * Real.exp (4000 * Real.sqrt Q) < T * J
  field_simp at hcancel'
  nlinarith only [hcancel']
