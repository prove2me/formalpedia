-- Prove2me | solution 2 for KServer.bcr_hard_chunk_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T00:32:14.937571+00:00
-- url     : https://prove2.me/submissions/c3a4a28f-f843-48cc-97fe-1c7e8d7a2d24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_bcr_space2
import Theorems.Thm_KServer_bcr_level_system
import Theorems.Thm_KServer_chunk_system_pad
import Theorems.Thm_KServer_chunk_window_variance

namespace KServer

/-- The level index chosen for `k`, and the two facts it must satisfy. -/
theorem level_index (β : ℕ) (hβ : 0 < β) (k : ℕ) (hk : 36 * (β + 1) ^ 2 ≤ k) :
    (β + 1) * 6 ^ (Nat.log 6 ((k + 1) / (β + 1))) ≤ k + 1 ∧
      Real.log k ≤ 2 * (Nat.log 6 ((k + 1) / (β + 1)) : ℝ) * Real.log 6 := by
  set q := (k + 1) / (β + 1) with hq
  set w := Nat.log 6 q with hw
  have hβ1 : 1 ≤ β + 1 := by omega
  have hk1 : 36 * (β + 1) ^ 2 ≤ k := hk
  have hqpos : 0 < q := by
    rw [hq]
    refine Nat.div_pos ?_ (by omega)
    nlinarith [sq_nonneg (β + 1)]
  constructor
  · -- cardinality: (β+1) * 6 ^ w ≤ k + 1
    have h1 : 6 ^ w ≤ q := Nat.pow_log_le_self 6 (by omega)
    calc (β + 1) * 6 ^ w ≤ (β + 1) * q := Nat.mul_le_mul_left _ h1
      _ = q * (β + 1) := by ring
      _ ≤ k + 1 := Nat.div_mul_le_self _ _
  · -- the logarithmic bound
    have hlt : q < 6 ^ (w + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
    have hk1lt : k + 1 < (q + 1) * (β + 1) := by
      have hdm : (β + 1) * ((k + 1) / (β + 1)) + (k + 1) % (β + 1) = k + 1 :=
        Nat.div_add_mod _ _
      have hmod : (k + 1) % (β + 1) < β + 1 := Nat.mod_lt (k + 1) (by omega)
      rw [← hq] at hdm
      calc k + 1 = (β + 1) * q + (k + 1) % (β + 1) := hdm.symm
        _ < (β + 1) * q + (β + 1) := Nat.add_lt_add_left hmod _
        _ = (q + 1) * (β + 1) := by ring
    have hchain : (k : ℕ) + 1 < 6 ^ (w + 1) * (β + 1) := by
      have : q + 1 ≤ 6 ^ (w + 1) := hlt
      calc k + 1 < (q + 1) * (β + 1) := hk1lt
        _ ≤ 6 ^ (w + 1) * (β + 1) := Nat.mul_le_mul_right _ this
    -- move to the reals
    have hkR : (k : ℝ) < 6 ^ (w + 1) * ((β : ℝ) + 1) := by
      have := hchain
      have h2 : ((k : ℝ) + 1) < (6 : ℝ) ^ (w + 1) * ((β : ℝ) + 1) := by
        exact_mod_cast hchain
      linarith
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := by nlinarith [sq_nonneg (β + 1)]
      exact_mod_cast this
    have hBpos : (0 : ℝ) < 6 * ((β : ℝ) + 1) := by positivity
    have hsplit : (6 : ℝ) ^ (w + 1) * ((β : ℝ) + 1)
        = (6 * ((β : ℝ) + 1)) * 6 ^ w := by ring
    have hlog1 : Real.log k < Real.log (6 * ((β : ℝ) + 1)) + (w : ℝ) * Real.log 6 := by
      have h3 : Real.log k < Real.log ((6 * ((β : ℝ) + 1)) * 6 ^ w) := by
        refine Real.log_lt_log hkpos ?_
        rw [← hsplit]; exact hkR
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h3
      linarith
    have hlog2 : 2 * Real.log (6 * ((β : ℝ) + 1)) ≤ Real.log k := by
      have hle : ((36 : ℝ) * ((β : ℝ) + 1) ^ 2) ≤ (k : ℝ) := by exact_mod_cast hk1
      have h4 : Real.log (36 * ((β : ℝ) + 1) ^ 2) ≤ Real.log k :=
        Real.log_le_log (by positivity) hle
      have h5 : (36 : ℝ) * ((β : ℝ) + 1) ^ 2 = (6 * ((β : ℝ) + 1)) ^ 2 := by ring
      rw [h5, Real.log_pow] at h4
      push_cast at h4
      linarith
    linarith

end KServer

open KServer

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ (m : MetricSpace (Fin (k + 1))) (s t : Fin (k + 1)) (cHi T price : ℝ) (M : ℕ),
        0 ≤ price ∧
        0 < @dist (Fin (k + 1)) m.toDist s t ∧
        c * Real.log k ^ 2 * @dist (Fin (k + 1)) m.toDist s t ≤ T ∧
        Nonempty (@ChunkSystemB (Fin (k + 1)) m s t 0 cHi T price M) := by
  obtain ⟨α, hα, β, hβ, H⟩ := bcr_level_system
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  refine ⟨α / (4 * Real.log 6 ^ 2), by positivity, 36 * (β + 1) ^ 2, fun k hk => ?_⟩
  set w := Nat.log 6 ((k + 1) / (β + 1)) with hw
  obtain ⟨hcard, hlogk⟩ := level_index β hβ k hk
  -- the level-`w` system
  obtain ⟨cHi, price, M, C, hprice, h0triv⟩ := H w
  -- its space has at most `k + 1` points, and the marked points are far apart
  have hcard' : Fintype.card (bcrLevel2 β hβ w).carrier ≤ k + 1 :=
    le_trans (bcrLevel2_card_le β hβ w) hcard
  have hdist := bcrLevel2_dist_st β hβ w
  have hβR : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have hdpos : (0 : ℝ) < (β : ℝ) * 3 ^ w := by positivity
  -- pad the space out to exactly `k + 1` points
  letI := (bcrLevel2 β hβ w).fin
  letI := (bcrLevel2 β hβ w).metric
  obtain ⟨m, a, b, hab, C', h0triv', -⟩ :=
    chunk_system_pad (X := (bcrLevel2 β hβ w).carrier) k hcard' C h0triv
      (V := ((C.m : ℝ) * (cHi - 0)) ^ 2) (chunk_window_variance C)
  refine ⟨m, a, b, cHi, α * (w : ℝ) ^ 2 * ((β : ℝ) * 3 ^ w), price, M, hprice, ?_, ?_, ⟨C'⟩⟩
  · rw [hab, hdist]; exact hdpos
  · rw [hab, hdist]
    -- `c log² k · d ≤ α w² · d`
    have hlogk0 : 0 ≤ Real.log k := by
      have : (1 : ℝ) ≤ (k : ℝ) := by
        have : 1 ≤ k := by nlinarith [sq_nonneg (β + 1)]
        exact_mod_cast this
      exact Real.log_nonneg this
    have hsq : Real.log k ^ 2 ≤ 4 * (w : ℝ) ^ 2 * Real.log 6 ^ 2 := by
      have h1 : Real.log k ^ 2 ≤ (2 * (w : ℝ) * Real.log 6) ^ 2 := by
        apply sq_le_sq' <;> nlinarith [hlogk, hlogk0]
      nlinarith [h1]
    have hcoef : α / (4 * Real.log 6 ^ 2) * Real.log k ^ 2 ≤ α * (w : ℝ) ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hsq, hα.le]
    nlinarith [mul_le_mul_of_nonneg_right hcoef hdpos.le]
