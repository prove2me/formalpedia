-- Prove2me | solution 2 for mme_CW_q6_coupled_primary_hash_Ctensor_quarter_root
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:31:02.63799+00:00
-- url     : https://prove2.me/submissions/5e7da938-3a34-4371-bb77-3b44655ea6f8

import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss
import Theorems.Thm_mme_CW_q6_coupled_survivor_square_isomorphic
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Mathlib.Tactic

open MME BigOperators Filter
universe u
set_option autoImplicit false

/-- Selecting a cubical number of copies loses at most a factor of eight. -/
private theorem cube_prefix_eighth (k : ℕ) :
    ∃ A : ℕ, A ^ 3 ≤ k ∧ k ≤ 8 * A ^ 3 := by
  by_cases hk : k = 0
  · subst k
    exact ⟨0, by norm_num, by norm_num⟩
  let A := Nat.findGreatest (fun a ↦ a ^ 3 ≤ k) k
  have hA : 1 ≤ A := Nat.le_findGreatest (P := fun a ↦ a ^ 3 ≤ k) (by omega) (by simpa using Nat.one_le_iff_ne_zero.mpr hk)
  have hAk : A ^ 3 ≤ k := Nat.findGreatest_spec (P := fun a ↦ a ^ 3 ≤ k) (Nat.zero_le k) (by simp)
  have hnext : k < (A + 1) ^ 3 := by
    by_contra hn
    have hp : (A + 1) ^ 3 ≤ k := by omega
    have hb : A + 1 ≤ k := (le_self_pow (by omega) (by norm_num : (3 : ℕ) ≠ 0)).trans hp
    have := Nat.le_findGreatest (P := fun a ↦ a ^ 3 ≤ k) hb hp
    change A + 1 ≤ A at this
    omega
  refine ⟨A, hAk, ?_⟩
  have hbound : (A + 1) ^ 3 ≤ (2 * A) ^ 3 := by
    gcongr
    omega
  calc
    k ≤ (A + 1) ^ 3 := hnext.le
    _ ≤ (2 * A) ^ 3 := hbound
    _ = 8 * A ^ 3 := by ring


theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
      let raw : ℝ :=
        4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ A H : ℕ,
        0 < H ∧
        H ≤ 4 ^ N ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
            TensorObj.kron (MMObj K H H H)
              (coupledQ6Survivor K L Gcount)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        (raw * Real.exp (-(loss / 2))) ^ (2 * N) ≤
          (((A ^ 3 : ℕ) : ℝ) * ((H : ℝ) ^ 2)) *
            (((side * side * side : ℕ) : ℝ) ^ tau) := by
  classical
  obtain ⟨D, hD, hcap⟩ :=
    mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss (K := K) tau htau
  let E : ℝ := D + Real.log 8
  have hlog : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
  have hE : 0 ≤ E := add_nonneg hD hlog
  have hnat : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hroot : Tendsto (fun N : ℕ ↦ Real.sqrt (Real.sqrt ((N + 1 : ℕ) : ℝ)))
      atTop atTop := Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hnat)
  filter_upwards [hcap, eventually_ge_atTop (1 : ℕ), hroot.eventually_ge_atTop (2 * E)]
    with N hcap hN hroot
  dsimp only
  intro _
  let L : ℕ := ⌊2 / ((6 : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let s : ℕ := 6 ^ (4 * G + 2 * L)
  let S : TensorObj K 3 := coupledQ6Survivor K L G
  let raw : ℝ := 4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  let t : ℝ := Real.sqrt (Real.sqrt ((N + 1 : ℕ) : ℝ))
  let w : ℝ := (((s ^ 3 : ℕ) : ℝ) ^ tau)
  obtain ⟨k, hr, hk⟩ := hcap
  obtain ⟨A, hAk, hkA⟩ := cube_prefix_eighth k
  have hunit : TensorObj.Isomorphic (TensorObj.kron (MMObj K 1 1 1) S) S := by
    apply TensorQ.toQ_eq_iff.mp
    rw [TensorQ.toQ_kron]
    change MMq K 1 1 1 * TensorQ.toQ S = TensorQ.toQ S
    rw [MMq_one, one_mul]
  have hblock : TensorObj.Restrict (TensorObj.kron (MMObj K 1 1 1) S)
      (MMObj K s s s) :=
    hunit.1.trans (mme_CW_q6_coupled_survivor_square_isomorphic (K := K) L G).1
  have hpref := mme_bigAdd_prefix_restrict (K := K) (d := 3) (by omega)
    hAk (fun _ : Fin k ↦ MMObj K s s s)
  have hHbound : 1 ≤ (4 : ℕ) ^ N := by
    have hp : 0 < (4 : ℕ) ^ N := by positivity
    omega
  refine ⟨A, 1, by norm_num, hHbound,
    (mme_bigAdd_mono_restrict (fun _ : Fin (A ^ 3) ↦ hblock)).trans (hpref.trans hr), ?_⟩
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  have hside : side = s := by
    dsimp [side, s]
    calc
      _ = (6 ^ 2) ^ (2 * G) * 6 ^ (2 * L) := by norm_num
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  simp only [Nat.cast_one, one_pow, mul_one]
  change (raw * Real.exp (-(t⁻¹ / 2))) ^ (2 * N) ≤
    ((A ^ 3 : ℕ) : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau)
  rw [hside]
  have hcube : s * s * s = s ^ 3 := by ring
  simp only [hcube]
  change (raw * Real.exp (-(t⁻¹ / 2))) ^ (2 * N) ≤ ((A ^ 3 : ℕ) : ℝ) * w
  have hx : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hu : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hx
  have ht : 0 < t := Real.sqrt_pos.mpr hu
  have hu_sq := Real.sq_sqrt hx.le
  have ht_sq : t ^ 2 = Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sq_sqrt hu.le
  have hn : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show N + 1 ≤ 2 * N by omega)
  have hEt : 2 * E * t ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hroot ht.le
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hEt hu.le
  have hbudget : E * Real.sqrt ((N + 1 : ℕ) : ℝ) * t ≤ (N : ℝ) := by
    nlinarith
  have hu1 : 1 ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    nlinarith
  have hlogscale : Real.log (8 : ℝ) ≤ Real.log 8 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    nlinarith
  have hexparg : Real.log 8 + ((2 * N : ℕ) : ℝ) * (-(t⁻¹ / 2)) ≤
      -D * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_right hlogscale ht.le
    apply (mul_le_mul_iff_of_pos_right ht).mp
    push_cast
    field_simp
    dsimp [E] at hbudget
    push_cast at hbudget hscaled
    nlinarith
  have hloss : 8 * (raw * Real.exp (-(t⁻¹ / 2))) ^ (2 * N) ≤
      raw ^ (2 * N) * Real.exp (-D * Real.sqrt ((N + 1 : ℕ) : ℝ)) := by
    have he := Real.exp_le_exp.mpr hexparg
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8), Real.exp_nat_mul] at he
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ raw ^ (2 * N) by positivity)
    simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hh
  have hcount : (k : ℝ) * w ≤ 8 * (((A ^ 3 : ℕ) : ℝ) * w) := by
    have hcast : (k : ℝ) ≤ 8 * ((A ^ 3 : ℕ) : ℝ) := by exact_mod_cast hkA
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcast
      (show 0 ≤ w from Real.rpow_nonneg (by positivity) tau)
  apply (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 8)).mp
  exact hloss.trans (hk.trans hcount)

#print axioms solution
