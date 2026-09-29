-- Prove2me | solution 1 for KServer.bcr_chunk_system_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T13:09:20.85877+00:00
-- url     : https://prove2.me/submissions/64631291-5577-404b-97f7-ad41b062217e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Theorems.Thm_KServer_bcr_level_family

open KServer

namespace KServerAux

/-- If `k` is at least `36 (β+1)^2`, the level chosen by the assembly is deep
enough that `6 (β + 1) ≤ 6 ^ w`. -/
theorem six_mul_le_pow (β k : ℕ) (hk : 36 * (β + 1) ^ 2 ≤ k) :
    6 * (β + 1) ≤ 6 ^ Nat.log 6 ((k + 1) / (β + 1)) := by
  set q := (k + 1) / (β + 1) with hq
  have hq36 : 36 * (β + 1) ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le (Nat.succ_pos β)]
    nlinarith [hk]
  have hlt : q < 6 ^ (Nat.log 6 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have h1 : 36 * (β + 1) < 6 ^ (Nat.log 6 q + 1) := lt_of_le_of_lt hq36 hlt
  have h2 : 6 ^ (Nat.log 6 q + 1) = 6 * 6 ^ Nat.log 6 q := by ring
  omega

end KServerAux

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ (X : Type) (mX : MetricSpace X) (fX : Fintype X) (s t : X),
        @Fintype.card X fX ≤ k + 1 ∧
        0 < @dist X mX.toDist s t ∧
        ∃ (cHi T price : ℝ) (M : ℕ) (C : @ChunkSystemB X mX s t 0 cHi T price M),
          0 ≤ price ∧
          c * Real.log k ^ 2 * @dist X mX.toDist s t ≤ T ∧
          (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) := by
  obtain ⟨α, hα, β, hβ, H⟩ := KServer.bcr_level_family
  have hlog6 : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  refine ⟨α / (4 * Real.log 6 ^ 2), by positivity, 36 * (β + 1) ^ 2 + 1, ?_⟩
  intro k hk
  have hk36 : 36 * (β + 1) ^ 2 ≤ k := by omega
  set q := (k + 1) / (β + 1) with hqdef
  set w := Nat.log 6 q with hwdef
  obtain ⟨X, mX, fX, s, t, hcard, hdist, cHi, price, M, C, hprice, htriv⟩ := H w
  -- the level is deep enough
  have hdeep : 6 * (β + 1) ≤ 6 ^ w := KServerAux.six_mul_le_pow β k hk36
  -- cardinality
  have hq36 : 36 * (β + 1) ≤ q := by
    rw [hqdef, Nat.le_div_iff_mul_le (Nat.succ_pos β)]
    nlinarith [hk36]
  have hqpos : 0 < q := by omega
  have hpowle : 6 ^ w ≤ q := Nat.pow_log_le_self 6 (by omega)
  have hcardk : (β + 1) * 6 ^ w ≤ k + 1 := by
    calc (β + 1) * 6 ^ w ≤ (β + 1) * q := Nat.mul_le_mul_left _ hpowle
      _ ≤ k + 1 := Nat.mul_div_le (k + 1) (β + 1)
  -- distance is positive
  have hdpos : (0 : ℝ) < (β : ℝ) * 3 ^ w := by
    have : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
    positivity
  -- the logarithmic estimate
  have hklt : k < (β + 1) * 6 ^ (w + 1) := by
    have hlt : q < 6 ^ (w + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
    have hkq : k + 1 ≤ (β + 1) * q + β := by
      have hdm := Nat.div_add_mod (k + 1) (β + 1)
      have hmod : (k + 1) % (β + 1) ≤ β :=
        Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos β))
      rw [hqdef]
      omega
    have hstep : (β + 1) * (q + 1) ≤ (β + 1) * 6 ^ (w + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexpand : (β + 1) * (q + 1) = (β + 1) * q + (β + 1) := by ring
    omega
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have : 1 ≤ k := by omega
    exact_mod_cast this
  have hlogk : Real.log k ≤ Real.log (β + 1) + ((w : ℝ) + 1) * Real.log 6 := by
    have hcast : (k : ℝ) ≤ ((β : ℝ) + 1) * 6 ^ (w + 1) := by
      have : (k : ℝ) ≤ (((β + 1) * 6 ^ (w + 1) : ℕ) : ℝ) := by
        exact_mod_cast le_of_lt hklt
      simpa using this
    have h1 : Real.log k ≤ Real.log (((β : ℝ) + 1) * 6 ^ (w + 1)) := by
      refine Real.log_le_log (by linarith) hcast
    have h2 : Real.log (((β : ℝ) + 1) * 6 ^ (w + 1))
        = Real.log ((β : ℝ) + 1) + ((w : ℝ) + 1) * Real.log 6 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [h2] at h1
    simpa using h1
  have hbeta : Real.log ((β : ℝ) + 1) + Real.log 6 ≤ (w : ℝ) * Real.log 6 := by
    have hcast : (6 : ℝ) * ((β : ℝ) + 1) ≤ 6 ^ w := by
      have : ((6 * (β + 1) : ℕ) : ℝ) ≤ ((6 ^ w : ℕ) : ℝ) := by exact_mod_cast hdeep
      push_cast at this
      linarith
    have h1 : Real.log (6 * ((β : ℝ) + 1)) ≤ Real.log ((6 : ℝ) ^ w) :=
      Real.log_le_log (by positivity) hcast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    linarith
  have hfinal : Real.log k ≤ 2 * (w : ℝ) * Real.log 6 := by linarith
  have hlognn : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hsq : Real.log k ^ 2 ≤ 4 * (w : ℝ) ^ 2 * Real.log 6 ^ 2 := by
    have hw0 : (0 : ℝ) ≤ 2 * (w : ℝ) * Real.log 6 := le_trans hlognn hfinal
    nlinarith [hfinal, hlognn]
  refine ⟨X, mX, fX, s, t, ?_, ?_, cHi, α * (w : ℝ) ^ 2 * ((β : ℝ) * 3 ^ w), price, M, C,
    hprice, ?_, htriv⟩
  · exact le_trans hcard hcardk
  · rw [hdist]; exact hdpos
  · rw [hdist]
    have hcoef : α / (4 * Real.log 6 ^ 2) * Real.log k ^ 2 ≤ α * (w : ℝ) ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hsq, hα.le]
    have := mul_le_mul_of_nonneg_right hcoef hdpos.le
    linarith [this]
