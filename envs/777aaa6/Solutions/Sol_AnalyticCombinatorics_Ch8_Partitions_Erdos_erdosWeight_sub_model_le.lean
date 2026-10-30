-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.erdosWeight_sub_model_le
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:23:23.691914+00:00
-- url     : https://prove2.me/submissions/bbb9ae17-63df-4cb9-bb0c-9f8d04e47d02

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Mathlib

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

open scoped BigOperators

lemma sigmaR_eq_sum_divisors (m : ℕ) :
    sigmaR m = ∑ d ∈ m.divisors, (d : ℝ) := by
  rw [sigmaR, ArithmeticFunction.sigma_one_apply]
  norm_num

end AnalyticCombinatorics.Ch8.Partitions.Sigma
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma C_pos : 0 < C := by
  dsimp [C]
  positivity

lemma sigmaR_nonneg (n : ℕ) : 0 ≤ Sigma.sigmaR n := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  exact Finset.sum_nonneg fun d _hd => by positivity

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

section
/-!
# Mass-rate campaign: second-order kernel expansions (R8 §3.2–3.3)

Second-order expansions of the square-root drop and the reciprocal, with explicit
error constants:

* `sqrt_drop_second_order` — `|（√n−√(n−m)) − (m/(2s) + m²/(8s³))| ≤ m³/s⁵` for `m ≤ n`,
  via the purely algebraic identity `8s³E = (s−q)³(q+3s)` (`s=√n`, `q=√(n−m)`,
  `linear_combination` on `q² = s²−m`) — no calculus, no smallness hypothesis;
* `inv_sub_second_order` — `|1/(n−m) − (1/n + m/n²)| = m²/(n²(n−m)) ≤ 2m²/n³` for `2m ≤ n`.

Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/--
**Square-root drop, second order**: for `m ≤ n`, `1 ≤ n`,

  `|（√n − √(n−m)) − (m/(2√n) + m²/(8√n³))| ≤ m³/√n⁵`.
-/
lemma sqrt_drop_second_order {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    |(Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
        - ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
          + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))|
      ≤ (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  set q : ℝ := Real.sqrt ((n - m : ℕ) : ℝ) with hqdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm]
    ring
  have hq2 : q ^ 2 = s ^ 2 - (m : ℝ) := by
    rw [hqdef, Real.sq_sqrt (Nat.cast_nonneg _), hcast, hs2]
  have hqs : q ≤ s := by
    have h1 : q ^ 2 ≤ s ^ 2 := by
      rw [hq2]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    nlinarith [hq0, hs.le]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- the key polynomial identity: 8s⁴ − 8s³q − 4s²m − m² = (s−q)³(q+3s)
  have hkey : 8 * s ^ 4 - 8 * s ^ 3 * q - 4 * s ^ 2 * (m : ℝ) - (m : ℝ) ^ 2
      = (s - q) ^ 3 * (q + 3 * s) := by
    linear_combination (q ^ 2 - 5 * s ^ 2 - (m : ℝ)) * hq2
  -- the expression E in closed form
  have hE_eq : (s - q) - ((m : ℝ) / (2 * s) + (m : ℝ) ^ 2 / (8 * s ^ 3))
      = (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3) := by
    rw [← hkey]
    field_simp
    ring
  -- nonnegativity and the bound
  have hsq_nonneg : 0 ≤ s - q := by linarith
  have hE_nonneg : 0 ≤ (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3) := by
    have h1 : 0 ≤ (s - q) ^ 3 := by positivity
    have h2 : 0 ≤ q + 3 * s := by linarith
    positivity
  rw [hE_eq, abs_of_nonneg hE_nonneg]
  -- (s−q)(s+q) = m so s−q ≤ m/s; q+3s ≤ 4s
  have hprod : (s - q) * (s + q) = (m : ℝ) := by
    have : (s - q) * (s + q) = s ^ 2 - q ^ 2 := by ring
    rw [this, hq2]
    ring
  have hsq_le : s - q ≤ (m : ℝ) / s := by
    rw [le_div_iff₀ hs]
    calc (s - q) * s ≤ (s - q) * (s + q) :=
          mul_le_mul_of_nonneg_left (by linarith) hsq_nonneg
      _ = (m : ℝ) := hprod
  have hq3s : q + 3 * s ≤ 4 * s := by linarith
  calc (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3)
      ≤ ((m : ℝ) / s) ^ 3 * (4 * s) / (8 * s ^ 3) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul _ hq3s (by linarith) (by positivity)
        exact pow_le_pow_left₀ hsq_nonneg hsq_le 3
    _ = (m : ℝ) ^ 3 / (2 * s ^ 5) := by
        field_simp
        ring
    _ ≤ (m : ℝ) ^ 3 / s ^ 5 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [pow_pos hs 5]

/-- The sqrt-drop second-order remainder is nonnegative (same identity, factors `≥ 0`). -/
lemma sqrt_drop_second_order_nonneg {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    0 ≤ (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
        - ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
          + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  set q : ℝ := Real.sqrt ((n - m : ℕ) : ℝ) with hqdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm]
    ring
  have hq2 : q ^ 2 = s ^ 2 - (m : ℝ) := by
    rw [hqdef, Real.sq_sqrt (Nat.cast_nonneg _), hcast, hs2]
  have hqs : q ≤ s := by
    have h1 : q ^ 2 ≤ s ^ 2 := by
      rw [hq2]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    nlinarith [hq0, hs.le]
  have hkey : 8 * s ^ 4 - 8 * s ^ 3 * q - 4 * s ^ 2 * (m : ℝ) - (m : ℝ) ^ 2
      = (s - q) ^ 3 * (q + 3 * s) := by
    linear_combination (q ^ 2 - 5 * s ^ 2 - (m : ℝ)) * hq2
  have hE_eq : (s - q) - ((m : ℝ) / (2 * s) + (m : ℝ) ^ 2 / (8 * s ^ 3))
      = (s - q) ^ 3 * (q + 3 * s) / (8 * s ^ 3) := by
    rw [← hkey]
    field_simp
    ring
  rw [hE_eq]
  have h1 : 0 ≤ (s - q) ^ 3 := by
    have : 0 ≤ s - q := by linarith
    positivity
  have h2 : 0 ≤ q + 3 * s := by linarith
  positivity

/--
**Reciprocal, second order**: for `2m ≤ n`, `1 ≤ n`,

  `|1/(n−m) − (1/n + m/n²)| ≤ 2m²/n³`  (exactly `m²/(n²(n−m))`).
-/
lemma inv_sub_second_order {n m : ℕ} (hn : 1 ≤ n) (h2m : 2 * m ≤ n) :
    |1 / (((n - m : ℕ) : ℝ)) - (1 / (n : ℝ) + (m : ℝ) / (n : ℝ) ^ 2)|
      ≤ 2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 3 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm_le : m ≤ n := by omega
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm_le]
    ring
  have h2mR : 2 * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2m
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hnm_half : (n : ℝ) / 2 ≤ ((n - m : ℕ) : ℝ) := by
    rw [hcast]
    linarith
  have hnm_pos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by linarith
  -- exact identity
  have hexact : 1 / (((n - m : ℕ) : ℝ)) - (1 / (n : ℝ) + (m : ℝ) / (n : ℝ) ^ 2)
      = (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ((n - m : ℕ) : ℝ)) := by
    have hne2 : (n : ℝ) - (m : ℝ) ≠ 0 := by
      rw [← hcast]
      exact hnm_pos.ne'
    rw [hcast]
    field_simp
    ring
  rw [hexact, abs_of_nonneg (by positivity)]
  -- m²/(n²(n−m)) ≤ m²/(n²·n/2) = 2m²/n³
  calc (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ((n - m : ℕ) : ℝ))
      ≤ (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ((n : ℝ) / 2)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left hnm_half (by positivity)
    _ = 2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 3 := by
        field_simp

/--
**Exponential drop, second order** (R8 §3.4): for `m ≤ n` with `4C·m² ≤ √n³`,

  `|e^{−C·drop} − e^{−(C/2)m/√n}·(1 − C·m²/(8√n³))|
      ≤ (C² + 2C)·e^{−(C/2)m/√n}·(m³/√n⁵ + m⁴/√n⁶)`.
-/
lemma exp_sqrt_drop_second_order {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n)
    (hsmall : 4 * C * (m : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) ^ 3) :
    |Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))
        - Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
            (1 - C * (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))|
      ≤ (C ^ 2 + 2 * C) *
          Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
          ((m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 + (m : ℝ) ^ 4 / Real.sqrt (n : ℝ) ^ 6) := by
  have hC := C_pos
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
  -- the remainder E and its bounds
  set E : ℝ := (s - Real.sqrt ((n - m : ℕ) : ℝ))
      - ((m : ℝ) / (2 * s) + (m : ℝ) ^ 2 / (8 * s ^ 3)) with hEdef
  have hE0 : 0 ≤ E := sqrt_drop_second_order_nonneg hn hm
  have hEle : E ≤ (m : ℝ) ^ 3 / s ^ 5 := by
    have := sqrt_drop_second_order hn hm
    rw [← hsdef, ← hEdef] at this
    calc E ≤ |E| := le_abs_self E
      _ ≤ (m : ℝ) ^ 3 / s ^ 5 := this
  -- m²/s³ ≤ 1/(4C), m/s² ≤ 1, m³/s⁵ ≤ 1/(4C)
  have hm2s3 : (m : ℝ) ^ 2 / s ^ 3 ≤ 1 / (4 * C) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsmall]
  have hms2 : (m : ℝ) / s ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    rw [hs2]
    exact hmn
  have hm3s5 : (m : ℝ) ^ 3 / s ^ 5 ≤ 1 / (4 * C) := by
    have heq : (m : ℝ) ^ 3 / s ^ 5 = ((m : ℝ) ^ 2 / s ^ 3) * ((m : ℝ) / s ^ 2) := by
      field_simp
    rw [heq]
    calc ((m : ℝ) ^ 2 / s ^ 3) * ((m : ℝ) / s ^ 2)
        ≤ (1 / (4 * C)) * 1 := by
          apply mul_le_mul hm2s3 hms2 (by positivity) (by positivity)
      _ = 1 / (4 * C) := mul_one _
  -- δ := C(m²/(8s³) + E) ∈ [0, 9/32]
  set δ : ℝ := C * ((m : ℝ) ^ 2 / (8 * s ^ 3) + E) with hδdef
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]
    have h1 : 0 ≤ (m : ℝ) ^ 2 / (8 * s ^ 3) := by positivity
    nlinarith [hE0, hC]
  have hδ_le : δ ≤ 9 / 32 := by
    rw [hδdef]
    have h1 : (m : ℝ) ^ 2 / (8 * s ^ 3) ≤ 1 / (32 * C) := by
      have heq : (m : ℝ) ^ 2 / (8 * s ^ 3) = ((m : ℝ) ^ 2 / s ^ 3) / 8 := by ring
      rw [heq]
      calc ((m : ℝ) ^ 2 / s ^ 3) / 8 ≤ (1 / (4 * C)) / 8 := by linarith [hm2s3]
        _ = 1 / (32 * C) := by ring
    have h2 : E ≤ 1 / (4 * C) := le_trans hEle hm3s5
    have h3 : (m : ℝ) ^ 2 / (8 * s ^ 3) + E ≤ 1 / (32 * C) + 1 / (4 * C) := by linarith
    calc C * ((m : ℝ) ^ 2 / (8 * s ^ 3) + E)
        ≤ C * (1 / (32 * C) + 1 / (4 * C)) :=
          mul_le_mul_of_nonneg_left h3 hC.le
      _ = 9 / 32 := by field_simp; ring
  have hδ1 : |(-δ : ℝ)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hδ0]
    linarith
  -- exponential split: e^{−C·drop} = e^{−(C/2)m/s}·e^{−δ}
  have hsplit : Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))
      = Real.exp (-(C / 2) * (m : ℝ) / s) * Real.exp (-δ) := by
    rw [← Real.exp_add]
    congr 1
    rw [hδdef, hEdef]
    field_simp
    ring
  -- |e^{−δ} − 1 + δ| ≤ δ²
  have hquad : |Real.exp (-δ) - 1 - (-δ)| ≤ (-δ) ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le hδ1
  -- assemble the difference
  have hbody : Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))
      - Real.exp (-(C / 2) * (m : ℝ) / s) * (1 - C * (m : ℝ) ^ 2 / (8 * s ^ 3))
      = Real.exp (-(C / 2) * (m : ℝ) / s) *
          ((Real.exp (-δ) - 1 + δ) - C * E) := by
    rw [hsplit, hδdef]
    ring
  rw [hbody, abs_mul, abs_of_pos (Real.exp_pos _)]
  -- bound the bracket: ≤ δ² + C·E ≤ (C²+2C)(m³/s⁵ + m⁴/s⁶)
  have hbracket : |(Real.exp (-δ) - 1 + δ) - C * E| ≤ δ ^ 2 + C * E := by
    have h1 : |Real.exp (-δ) - 1 + δ| ≤ δ ^ 2 := by
      have : Real.exp (-δ) - 1 + δ = Real.exp (-δ) - 1 - (-δ) := by ring
      rw [this]
      calc |Real.exp (-δ) - 1 - (-δ)| ≤ (-δ) ^ 2 := hquad
        _ = δ ^ 2 := by ring
    have h2 : |C * E| = C * E := abs_of_nonneg (by positivity)
    calc |(Real.exp (-δ) - 1 + δ) - C * E|
        ≤ |Real.exp (-δ) - 1 + δ| + |C * E| := abs_sub _ _
      _ ≤ δ ^ 2 + C * E := by rw [h2]; linarith
  -- δ² ≤ C²m⁴/(32s⁶) + C·m³/(2s⁵) via (a+b)² ≤ 2a²+2b² and m⁶/s¹⁰ ≤ m³/(4C·s⁵)
  have hδsq : δ ^ 2 ≤ C ^ 2 * (m : ℝ) ^ 4 / (32 * s ^ 6) + C * (m : ℝ) ^ 3 / (2 * s ^ 5) := by
    have hab : δ ^ 2 ≤ 2 * (C * ((m : ℝ) ^ 2 / (8 * s ^ 3))) ^ 2 + 2 * (C * E) ^ 2 := by
      rw [hδdef]
      nlinarith [sq_nonneg (C * ((m : ℝ) ^ 2 / (8 * s ^ 3)) - C * E)]
    have h1 : 2 * (C * ((m : ℝ) ^ 2 / (8 * s ^ 3))) ^ 2 = C ^ 2 * (m : ℝ) ^ 4 / (32 * s ^ 6) := by
      field_simp
      ring
    have h2 : 2 * (C * E) ^ 2 ≤ C * (m : ℝ) ^ 3 / (2 * s ^ 5) := by
      have hCE : C * E ≤ C * ((m : ℝ) ^ 3 / s ^ 5) := mul_le_mul_of_nonneg_left hEle hC.le
      have hCE2 : C * ((m : ℝ) ^ 3 / s ^ 5) ≤ C * (1 / (4 * C)) :=
        mul_le_mul_of_nonneg_left hm3s5 hC.le
      have hquarter : C * (1 / (4 * C)) = 1 / 4 := by field_simp
      have hCE0 : 0 ≤ C * E := by positivity
      calc 2 * (C * E) ^ 2 = 2 * (C * E) * (C * E) := by ring
        _ ≤ 2 * (1 / 4) * (C * ((m : ℝ) ^ 3 / s ^ 5)) := by
            apply mul_le_mul _ hCE hCE0 (by positivity)
            rw [← hquarter] at *
            nlinarith [hCE, hCE2, hCE0]
        _ = C * (m : ℝ) ^ 3 / (2 * s ^ 5) := by field_simp; ring
    linarith
  -- final assembly
  calc Real.exp (-(C / 2) * (m : ℝ) / s) * |(Real.exp (-δ) - 1 + δ) - C * E|
      ≤ Real.exp (-(C / 2) * (m : ℝ) / s) * (δ ^ 2 + C * E) :=
        mul_le_mul_of_nonneg_left hbracket (Real.exp_pos _).le
    _ ≤ Real.exp (-(C / 2) * (m : ℝ) / s) *
          ((C ^ 2 + 2 * C) * ((m : ℝ) ^ 3 / s ^ 5 + (m : ℝ) ^ 4 / s ^ 6)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have hCE_le : C * E ≤ C * ((m : ℝ) ^ 3 / s ^ 5) :=
          mul_le_mul_of_nonneg_left hEle hC.le
        have h2 : C ^ 2 * (m : ℝ) ^ 4 / (32 * s ^ 6) ≤ C ^ 2 * ((m : ℝ) ^ 4 / s ^ 6) := by
          rw [show C ^ 2 * (m : ℝ) ^ 4 / (32 * s ^ 6)
              = (C ^ 2 * (m : ℝ) ^ 4) / (32 * s ^ 6) by ring,
            show C ^ 2 * ((m : ℝ) ^ 4 / s ^ 6) = (C ^ 2 * (m : ℝ) ^ 4) / s ^ 6 by ring]
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [pow_pos hs 6]
        have h3 : C * (m : ℝ) ^ 3 / (2 * s ^ 5) ≤ C * ((m : ℝ) ^ 3 / s ^ 5) := by
          rw [show C * (m : ℝ) ^ 3 / (2 * s ^ 5) = (C * (m : ℝ) ^ 3) / (2 * s ^ 5) by ring,
            show C * ((m : ℝ) ^ 3 / s ^ 5) = (C * (m : ℝ) ^ 3) / s ^ 5 by ring]
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [pow_pos hs 5]
        have hpos1 : 0 ≤ C ^ 2 * ((m : ℝ) ^ 3 / s ^ 5) := by positivity
        have hpos2 : 0 ≤ 2 * C * ((m : ℝ) ^ 4 / s ^ 6) := by positivity
        have hfinal : δ ^ 2 + C * E
            ≤ C ^ 2 * ((m : ℝ) ^ 4 / s ^ 6) + 2 * C * ((m : ℝ) ^ 3 / s ^ 5) := by
          linarith [hδsq, hCE_le, h2, h3]
        have hexpand : (C ^ 2 + 2 * C) * ((m : ℝ) ^ 3 / s ^ 5 + (m : ℝ) ^ 4 / s ^ 6)
            = C ^ 2 * ((m : ℝ) ^ 4 / s ^ 6) + 2 * C * ((m : ℝ) ^ 3 / s ^ 5)
              + (C ^ 2 * ((m : ℝ) ^ 3 / s ^ 5) + 2 * C * ((m : ℝ) ^ 4 / s ^ 6)) := by
          ring
        linarith [hfinal, hpos1, hpos2, le_of_eq hexpand]
    _ = (C ^ 2 + 2 * C) *
          Real.exp (-(C / 2) * (m : ℝ) / s) *
          ((m : ℝ) ^ 3 / s ^ 5 + (m : ℝ) ^ 4 / s ^ 6) := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: explicit tail beyond the main range (R8 §4.1)

Beyond `m > n^{2/3}` (stated as `n² < m³` to stay cast-friendly) the kernel tail is
exponentially small:

  `Σ_{m: n² < m³} erdosWeight n m ≤ n³·e^{−(C/2)·n^{1/6}}`,

since `√n − √(n−m) ≥ m/(2√n) ≥ n^{1/6}/2`, `σ(m) ≤ m² ≤ n²`, `n−m ≥ 1`, and there are
at most `n` terms.  Far smaller than `1/n`.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The square-root drop dominates `m/(2√n)`. -/
lemma sqrt_drop_ge {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    (m : ℝ) / (2 * Real.sqrt (n : ℝ))
      ≤ Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  set q : ℝ := Real.sqrt ((n - m : ℕ) : ℝ) with hqdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm]
    ring
  have hq2 : q ^ 2 = s ^ 2 - (m : ℝ) := by
    rw [hqdef, Real.sq_sqrt (Nat.cast_nonneg _), hcast, hs2]
  have hqs : q ≤ s := by
    have h1 : q ^ 2 ≤ s ^ 2 := by
      rw [hq2]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    nlinarith [hq0, hs.le]
  have hprod : (s - q) * (s + q) = (m : ℝ) := by
    have h : (s - q) * (s + q) = s ^ 2 - q ^ 2 := by ring
    rw [h, hq2]
    ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s)]
  have hsum_le : s + q ≤ 2 * s := by linarith
  have hsq_nonneg : 0 ≤ s - q := by linarith
  calc (m : ℝ) = (s - q) * (s + q) := hprod.symm
    _ ≤ (s - q) * (2 * s) := mul_le_mul_of_nonneg_left hsum_le hsq_nonneg

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: combined coefficient expansion (R8 §3.5)

The main local brick: on the regime `1 ≤ m`, `2m ≤ n`, `4Cm² ≤ √n³`,

  `|1/(n−m)·e^{−C·drop} − (1/n)·e_m·(1 + m/n − Cm²/(8√n³))|
      ≤ (3C² + 5C + 2)·e_m·(m²/√n⁶ + m³/√n⁷ + m⁴/√n⁸)`,

where `e_m = e^{−(C/2)m/√n}`.  Decomposition `true = (A + r₁)(B·e_m + r₂)` with
`A = 1/n + m/n²`, `B = 1 − Cm²/(8s³)`; the only cross term is `A·B − M = −Cm³/(8s⁷)`
exactly; `r₁·(true exp) ≤ 2m²/s⁶·e_m` via `drop ≥ m/(2s)` (no exponent weakening
needed).  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/--
**Combined coefficient, second order** (R8 §3.5).
-/
lemma erdosWeight_coef_second_order {n m : ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m)
    (h2m : 2 * m ≤ n)
    (hsmall : 4 * C * (m : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) ^ 3) :
    |1 / (((n - m : ℕ) : ℝ)) *
        Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))
      - (1 / (n : ℝ)) * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
          (1 + (m : ℝ) / (n : ℝ)
            - C * (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))|
      ≤ (3 * C ^ 2 + 5 * C + 2) *
          Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
          ((m : ℝ) ^ 2 / Real.sqrt (n : ℝ) ^ 6
            + (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 7
            + (m : ℝ) ^ 4 / Real.sqrt (n : ℝ) ^ 8) := by
  have hC := C_pos
  have hm_le : m ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  set em : ℝ := Real.exp (-(C / 2) * (m : ℝ) / s) with hemdef
  have hem_pos : 0 < em := Real.exp_pos _
  -- pieces
  set A : ℝ := 1 / (n : ℝ) + (m : ℝ) / (n : ℝ) ^ 2 with hAdef
  set B : ℝ := 1 - C * (m : ℝ) ^ 2 / (8 * s ^ 3) with hBdef
  set r₁ : ℝ := 1 / (((n - m : ℕ) : ℝ)) - A with hr₁def
  set r₂ : ℝ := Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ))) - em * B with hr₂def
  have hr₁_abs : |r₁| ≤ 2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 3 := by
    rw [hr₁def, hAdef]
    exact inv_sub_second_order hn h2m
  have hr₂_abs : |r₂| ≤ (C ^ 2 + 2 * C) * em *
      ((m : ℝ) ^ 3 / s ^ 5 + (m : ℝ) ^ 4 / s ^ 6) := by
    rw [hr₂def, hemdef, hBdef]
    have := exp_sqrt_drop_second_order hn hm_le hsmall
    rw [← hsdef] at this
    convert this using 2
  -- the true exponential is at most em
  have hexp_le_em : Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ))) ≤ em := by
    rw [hemdef]
    apply Real.exp_le_exp.mpr
    have hdrop := sqrt_drop_ge hn hm_le
    rw [← hsdef] at hdrop
    have h1 : (m : ℝ) / (2 * s) ≤ s - Real.sqrt ((n - m : ℕ) : ℝ) := hdrop
    have h2 : -(C / 2) * (m : ℝ) / s = -C * ((m : ℝ) / (2 * s)) := by
      field_simp
    rw [h2]
    nlinarith [h1, hC]
  have hexp_pos : 0 < Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ))) := Real.exp_pos _
  -- decomposition: true − main = (A·B − M)·em + A·r₂ + r₁·(true exp)
  -- where M = (1/n)(1 + m/n − Cm²/(8s³)) and A·B − M = −C·m³/(8·n²·s³)
  have hcross : A * B - (1 / (n : ℝ)) *
      (1 + (m : ℝ) / (n : ℝ) - C * (m : ℝ) ^ 2 / (8 * s ^ 3))
      = -(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3)) := by
    rw [hAdef, hBdef]
    field_simp
    ring
  have hdecomp : 1 / (((n - m : ℕ) : ℝ)) *
      Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))
      - (1 / (n : ℝ)) * em *
          (1 + (m : ℝ) / (n : ℝ) - C * (m : ℝ) ^ 2 / (8 * s ^ 3))
      = (A * B - (1 / (n : ℝ)) *
          (1 + (m : ℝ) / (n : ℝ) - C * (m : ℝ) ^ 2 / (8 * s ^ 3))) * em
        + A * r₂
        + r₁ * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ))) := by
    rw [hr₁def, hr₂def]
    ring
  rw [hdecomp, hcross]
  -- bound the three pieces
  have hA_le : A ≤ 2 / (n : ℝ) := by
    rw [hAdef]
    have h1 : (m : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hnpos]
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm_le
      nlinarith
    have h2 : (2 : ℝ) / (n : ℝ) = 1 / (n : ℝ) + 1 / (n : ℝ) := by ring
    linarith [le_of_eq h2]
  have hA_pos : 0 < A := by
    rw [hAdef]
    positivity
  -- piece 1: |cross·em| = C·m³/(8n²s³)·em = C·m³/(8s⁷)·em
  have hp1 : |(-(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))) * em|
      = C * (m : ℝ) ^ 3 / (8 * s ^ 7) * em := by
    rw [abs_mul, abs_neg, abs_of_pos hem_pos,
      abs_of_pos (by positivity : (0:ℝ) < C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))]
    congr 1
    rw [show (n : ℝ) ^ 2 = (s ^ 2) ^ 2 by rw [hs2]]
    ring
  -- piece 2: |A·r₂| ≤ (2/n)·bound = (2C²+4C)·em·(m³/s⁷ + m⁴/s⁸)
  have hp2 : |A * r₂| ≤ (2 * C ^ 2 + 4 * C) * em *
      ((m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8) := by
    rw [abs_mul, abs_of_pos hA_pos]
    calc A * |r₂|
        ≤ (2 / (n : ℝ)) * ((C ^ 2 + 2 * C) * em *
            ((m : ℝ) ^ 3 / s ^ 5 + (m : ℝ) ^ 4 / s ^ 6)) := by
          apply mul_le_mul hA_le hr₂_abs (abs_nonneg _) (by positivity)
      _ = (2 * C ^ 2 + 4 * C) * em *
            ((m : ℝ) ^ 3 / ((n:ℝ) * s ^ 5) + (m : ℝ) ^ 4 / ((n:ℝ) * s ^ 6)) := by
          field_simp
          ring
      _ = (2 * C ^ 2 + 4 * C) * em *
            ((m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8) := by
          rw [show (n : ℝ) * s ^ 5 = s ^ 7 by rw [← hs2]; ring,
            show (n : ℝ) * s ^ 6 = s ^ 8 by rw [← hs2]; ring]
  -- piece 3: |r₁·exp| ≤ (2m²/n³)·em = 2·em·m²/s⁶
  have hp3 : |r₁ * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))|
      ≤ 2 * em * ((m : ℝ) ^ 2 / s ^ 6) := by
    rw [abs_mul, abs_of_pos hexp_pos]
    calc |r₁| * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))
        ≤ (2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 3) * em := by
          apply mul_le_mul hr₁_abs hexp_le_em hexp_pos.le (by positivity)
      _ = 2 * em * ((m : ℝ) ^ 2 / s ^ 6) := by
          rw [show (n : ℝ) ^ 3 = s ^ 6 by rw [← hs2]; ring]
          ring
  -- triangle inequality and final collection
  calc |(-(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))) * em
        + A * r₂
        + r₁ * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))|
      ≤ |(-(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))) * em
          + A * r₂|
        + |r₁ * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))| := abs_add_le _ _
    _ ≤ (|(-(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))) * em| + |A * r₂|)
        + |r₁ * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))| := by
          linarith [abs_add_le ((-(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))) * em) (A * r₂)]
    _ ≤ C * (m : ℝ) ^ 3 / (8 * s ^ 7) * em
        + (2 * C ^ 2 + 4 * C) * em * ((m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8)
        + 2 * em * ((m : ℝ) ^ 2 / s ^ 6) := by
          rw [hp1] at *
          linarith [hp2, hp3]
    _ ≤ (3 * C ^ 2 + 5 * C + 2) * em *
          ((m : ℝ) ^ 2 / s ^ 6 + (m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8) := by
        have hY2 : 0 ≤ em * ((m : ℝ) ^ 2 / s ^ 6) := by positivity
        have hY3 : 0 ≤ em * ((m : ℝ) ^ 3 / s ^ 7) := by positivity
        have hY4 : 0 ≤ em * ((m : ℝ) ^ 4 / s ^ 8) := by positivity
        have c2 : (0 : ℝ) ≤ 3 * C ^ 2 + 5 * C := by positivity
        have c3 : (0 : ℝ) ≤ C ^ 2 + 7 * C / 8 + 2 := by positivity
        have c4 : (0 : ℝ) ≤ C ^ 2 + C + 2 := by positivity
        have key : (C / 8) * (em * ((m : ℝ) ^ 3 / s ^ 7))
            + ((2 * C ^ 2 + 4 * C) * (em * ((m : ℝ) ^ 3 / s ^ 7))
              + (2 * C ^ 2 + 4 * C) * (em * ((m : ℝ) ^ 4 / s ^ 8)))
            + 2 * (em * ((m : ℝ) ^ 2 / s ^ 6))
            ≤ (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 2 / s ^ 6))
              + (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 3 / s ^ 7))
              + (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 4 / s ^ 8)) := by
          nlinarith [mul_nonneg c2 hY2, mul_nonneg c3 hY3, mul_nonneg c4 hY4]
        calc C * (m : ℝ) ^ 3 / (8 * s ^ 7) * em
              + (2 * C ^ 2 + 4 * C) * em * ((m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8)
              + 2 * em * ((m : ℝ) ^ 2 / s ^ 6)
            = (C / 8) * (em * ((m : ℝ) ^ 3 / s ^ 7))
              + ((2 * C ^ 2 + 4 * C) * (em * ((m : ℝ) ^ 3 / s ^ 7))
                + (2 * C ^ 2 + 4 * C) * (em * ((m : ℝ) ^ 4 / s ^ 8)))
              + 2 * (em * ((m : ℝ) ^ 2 / s ^ 6)) := by ring
          _ ≤ (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 2 / s ^ 6))
              + (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 3 / s ^ 7))
              + (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 4 / s ^ 8)) := key
          _ = (3 * C ^ 2 + 5 * C + 2) * em *
              ((m : ℝ) ^ 2 / s ^ 6 + (m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8) := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Mass-rate campaign: §5 the second-order divisor calc

`kernelMass n = ∑_{m=1}^{n-1} σ(m)/(n−m)·exp(−C(√n−√(n−m)))` versus
`kernelMassApprox2 n = (1/n)M₀(t)+(1/n²)M₁(t)−(C/(8n²√n))M₂(t)` at `t=λ/√n`.

Brick 1 here: `kernelMassApprox2 n = ∑' m, modelSummand n m`, where
`modelSummand n m = σ(m)·e^{−tm}·(1/n + m/n² − Cm²/(8n²√n))` — i.e. the moment package collapses
to a single divisor-weighted Lambert sum.  This is the object the per-term estimate
`erdosWeight_coef_second_order` (#97), multiplied by `σ(m)≥0`, is compared against.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 1000000
open Filter
open scoped Topology BigOperators
open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close
theorem solution {n m : ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m)
    (h2m : 2 * m ≤ n) (hsmall : 4 * C * (m:ℝ) ^ 2 ≤ Real.sqrt (n:ℝ) ^ 3) :
    |erdosWeight n m - modelSummand n m|
      ≤ Sigma.sigmaR m * ((3 * C ^ 2 + 5 * C + 2) *
          Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
          ((m:ℝ) ^ 2 / (n:ℝ) ^ 3 + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
            + (m:ℝ) ^ 4 / (n:ℝ) ^ 4)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hsqrt0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hsq : Real.sqrt (n:ℝ) ^ 2 = (n:ℝ) := Real.sq_sqrt hnpos.le
  have hσnn : 0 ≤ Sigma.sigmaR m := sigmaR_nonneg m
  have hmne : ¬ m = 0 := by omega
  -- exp argument identity (massLam = C/2, √n)
  have hexparg : -(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)
      = -(C / 2) * (m:ℝ) / Real.sqrt (n:ℝ) := by rw [massLam]; ring
  -- √n powers in terms of n
  have hcube : Real.sqrt (n:ℝ) ^ 3 = (n:ℝ) * Real.sqrt (n:ℝ) := by
    linear_combination Real.sqrt (n:ℝ) * hsq
  have h6 : Real.sqrt (n:ℝ) ^ 6 = (n:ℝ) ^ 3 := by
    rw [show (6:ℕ) = 2 * 3 from rfl, pow_mul, hsq]
  have h7 : Real.sqrt (n:ℝ) ^ 7 = (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) := by
    rw [show (7:ℕ) = 6 + 1 from rfl, pow_succ, h6]
  have h8 : Real.sqrt (n:ℝ) ^ 8 = (n:ℝ) ^ 4 := by
    rw [show (8:ℕ) = 2 * 4 from rfl, pow_mul, hsq]
  -- factor σ out of erdosWeight and modelSummand
  have hweight : erdosWeight n m
      = Sigma.sigmaR m * (1 / ((n - m : ℕ):ℝ) *
          Real.exp (-C * (Real.sqrt (n:ℝ) - Real.sqrt ((n - m : ℕ):ℝ)))) := by
    rw [erdosWeight]; ring
  have hmodel : modelSummand n m
      = Sigma.sigmaR m * ((1 / (n:ℝ)) * Real.exp (-(C / 2) * (m:ℝ) / Real.sqrt (n:ℝ)) *
          (1 + (m:ℝ) / (n:ℝ) - C * (m:ℝ) ^ 2 / (8 * Real.sqrt (n:ℝ) ^ 3))) := by
    rw [modelSummand, if_neg hmne, hexparg, hcube]
    field_simp
  -- the difference is σ · (#97 inner expression)
  have hfac : erdosWeight n m - modelSummand n m
      = Sigma.sigmaR m * (1 / ((n - m : ℕ):ℝ) *
            Real.exp (-C * (Real.sqrt (n:ℝ) - Real.sqrt ((n - m : ℕ):ℝ)))
          - (1 / (n:ℝ)) * Real.exp (-(C / 2) * (m:ℝ) / Real.sqrt (n:ℝ)) *
            (1 + (m:ℝ) / (n:ℝ) - C * (m:ℝ) ^ 2 / (8 * Real.sqrt (n:ℝ) ^ 3))) := by
    rw [hweight, hmodel]; ring
  -- convert the stated RHS to #97's RHS
  have hRHS : (3 * C ^ 2 + 5 * C + 2) *
        Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
        ((m:ℝ) ^ 2 / (n:ℝ) ^ 3 + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
          + (m:ℝ) ^ 4 / (n:ℝ) ^ 4)
      = (3 * C ^ 2 + 5 * C + 2) *
        Real.exp (-(C / 2) * (m:ℝ) / Real.sqrt (n:ℝ)) *
        ((m:ℝ) ^ 2 / Real.sqrt (n:ℝ) ^ 6 + (m:ℝ) ^ 3 / Real.sqrt (n:ℝ) ^ 7
          + (m:ℝ) ^ 4 / Real.sqrt (n:ℝ) ^ 8) := by
    rw [hexparg, h6, h7, h8]
  rw [hfac, abs_mul, abs_of_nonneg hσnn, hRHS]
  exact mul_le_mul_of_nonneg_left
    (erdosWeight_coef_second_order hn hm1 h2m hsmall) hσnn
