-- Prove2me | solution 2 for mme_CW_q6_coupled_even_power_finite_extractions_below_raw
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T14:43:11.211745+00:00
-- url     : https://prove2.me/submissions/ac0465d1-50a5-44a8-a205-83f92243f5a2

import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_coupled_low_block_restrict
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_HasTauValueAtLeast_multiple_extractions_below
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_CW_q6_coupled_exact_floor_pruning

open MME BigOperators Filter Topology
universe u
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EvenExtraction

lemma eventual_round_power {V W : ℝ} (hV : 0 ≤ V) (hW : 1 ≤ W)
    (hVW : V < W) (e : ℕ) (he : 0 < e) :
    ∀ᶠ N : ℕ in atTop, V^N ≤ W^(N/e*e) := by
  have hWp : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hr0 : 0 ≤ V/W := div_nonneg hV hWp.le
  have hr1 : V/W < 1 := (div_lt_one hWp).2 hVW
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (W^e)
  have hh : ∀ᶠ N : ℕ in atTop, W^e * (V/W)^N ≤ 1 := by
    have hlim : Tendsto (fun N : ℕ => W^e*(V/W)^N) atTop (nhds 0) := by
      simpa using ht
    exact (hlim.eventually_lt_const (by norm_num : (0:ℝ)<1)).mono fun _ h => h.le
  filter_upwards [hh] with N hN
  have hc : W^e * V^N ≤ W^N := by
    have hdiv : (W^e * V^N) / W^N ≤ 1 := by
      simpa only [div_pow, mul_div_assoc] using hN
    simpa only [one_mul] using (div_le_iff₀ (pow_pos hWp N)).mp hdiv
  have hrem : W^(N%e) ≤ W^e :=
    pow_le_pow_right₀ hW (Nat.mod_lt N he).le
  have hp : W^N = W^(N/e*e) * W^(N%e) := by
    rw [← pow_add, Nat.mul_comm (N/e) e, Nat.div_add_mod]
  rw [hp] at hc
  have hu := hc.trans (mul_le_mul_of_nonneg_left hrem (pow_nonneg hWp.le _))
  nlinarith [pow_pos hWp e]

lemma eventual_extractions {K : Type u} [Field K]
    (T : TensorObj K 3) (tau V W B : ℝ)
    (hunit : (tensorPreorder K).le 1 (TensorQ.toQ T))
    (hV : 0 ≤ V) (hW : 1 ≤ W) (hVW : V < W) (hWB : W < B)
    (hB : HasTauValueAtLeast T tau B) :
    ∀ᶠ N : ℕ in atTop, ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
        (T.kronPow N) ∧ V^N ≤ ∑ i, (((a i*b i*c i : ℕ):ℝ)^tau) := by
  have hBp : 0 < B := by linarith
  obtain ⟨e,he,hE⟩ := mme_HasTauValueAtLeast_multiple_extractions_below
    T tau B W hBp (by linarith) hWB hB
  let P := tensorPreorder K
  letI : Preorder (TensorQ K 3) := P.toPreorder
  have hmono : Monotone (fun n : ℕ => (TensorQ.toQ T)^n) := by
    apply monotone_nat_of_le_succ
    intro n
    have h := P.mul_right 1 (TensorQ.toQ T) hunit ((TensorQ.toQ T)^n)
    simpa only [one_mul, pow_succ, mul_comm] using h
  filter_upwards [eventual_round_power hV hW hVW e he] with N hN
  obtain ⟨k,a,b,c,hr,hvalue⟩ := hE (N/e)
  refine ⟨k,a,b,c,hr.trans ?_,hN.trans hvalue⟩
  change P.le (TensorQ.toQ (T.kronPow (N/e*e))) (TensorQ.toQ (T.kronPow N))
  rw [TensorQ.toQ_kronPow, TensorQ.toQ_kronPow]
  exact hmono (Nat.div_mul_le_self N e)

lemma coupled_unit {K : Type u} [Field K] :
    (tensorPreorder K).le 1
      (TensorQ.toQ (cyclicSymmetrization (coupledObj K 6))) := by
  have hlow := mme_CW_coupled_low_block_restrict (K := K) 6
  have hcyc := mme_cyclicSymmetrization_mono_restrict hlow
  have hiso := mme_MMObj_cyclicSymmetrization_iso (K := K) 1 6 1
  have hr : TensorObj.Restrict (MMObj K 6 6 6)
      (cyclicSymmetrization (coupledObj K 6)) := by
    simpa using hiso.2.trans hcyc
  have hm := MMq_le_of_le (K := K) (n := 1) (n' := 6)
    (m := 1) (m' := 6) (p := 1) (p' := 6)
    (by norm_num) (by norm_num) (by norm_num)
  rw [MMq_one] at hm
  exact (tensorPreorder K).le_trans _ _ _ hm hr

end EvenExtraction

theorem solution {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3*tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < 4*(6:ℝ)^(3*tau)*((6:ℝ)^(3*tau)+2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6:ℝ)^(3*tau)+2)
      let L : ℕ := ⌊lambda*(N:ℝ)⌋₊
      let G : ℕ := N-L
      0<L ∧ L+G=N ∧ 341*L<100*G ∧
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2*N)) ∧
        V^(2*N) ≤ ∑ i, (((a i*b i*c i:ℕ):ℝ)^tau) := by
  let R : ℝ := 4*(6:ℝ)^(3*tau)*((6:ℝ)^(3*tau)+2)
  have hp : (36:ℝ) ≤ (6:ℝ)^(3*tau) := by
    calc (36:ℝ) = (6:ℝ)^(2:ℝ) := by norm_num
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) htau
  have hR : 1 < R := by dsimp [R]; nlinarith
  have hm : max V 1 < R := max_lt_iff.2 ⟨hVlt,hR⟩
  let W := (max V 1 + R)/2
  let B := (W+R)/2
  have hW1 : 1 ≤ W := by dsimp [W]; have := le_max_right V 1; linarith
  have hVW : V < W := by dsimp [W]; have := le_max_left V 1; linarith
  have hWR : W < R := by dsimp [W]; linarith
  have hWB : W < B := by dsimp [B]; linarith
  have hBR : B < R := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := by linarith
  have hval := mme_CW_q6_coupled_raw_cyclic_value_below (K := K) tau htau B hB0 hBR
  have hex := EvenExtraction.eventual_extractions
    (cyclicSymmetrization (coupledObj K 6)) tau V W B
    EvenExtraction.coupled_unit hV hW1 hVW hWB hval
  have htwo : Tendsto (fun N : ℕ => 2*N) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b,fun N hN => by omega⟩
  filter_upwards [mme_CW_q6_coupled_exact_floor_pruning tau htau, htwo.eventually hex]
    with N hprune hfinite
  exact ⟨hprune.1,hprune.2.1,hprune.2.2,hfinite⟩
