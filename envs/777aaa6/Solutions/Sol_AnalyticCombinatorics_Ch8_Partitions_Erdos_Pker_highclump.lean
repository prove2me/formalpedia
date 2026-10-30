-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_highclump
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:32:14.292693+00:00
-- url     : https://prove2.me/submissions/b68cd4d0-a467-4f21-9d8e-bf8bd375138d

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Mathlib

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
# R7 Fact B via Doeblin: the comparable-rank minorization is ELEMENTARY (via σ(m) ≥ m)

The windowed Doeblin minorization `δ ≤ ∑_k min(Pker x k, Pker y k)` for comparable starts does NOT need
σ-averaging / a local-limit theorem.  The key is `σ(m) ≥ m` (since `m ∣ m`): on the jump window
`m ∈ [a√x, b√x]` this gives `σ(m) ≥ a√x`, so `∑ min(σ(jump_x), σ(jump_y))` over the `~(b−a)√x` common
landings is `Θ(x)`, and the smooth factor `(1/k)·exp(−C(√x−√k))/kernelMass x` is `Θ(1)/x` there, yielding
`δ > 0`.  Purely elementary.  Opus-authored (attack vector found after ChatGPT framed the block route).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `σ(m) ≥ m` for `m ≥ 1` (since `m ∣ m`). -/
lemma sigmaR_ge_self {m : ℕ} (hm : 1 ≤ m) : (m : ℝ) ≤ Sigma.sigmaR m := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  have hmem : m ∈ m.divisors := Nat.mem_divisors_self m (by omega)
  calc (m : ℝ) = ∑ d ∈ ({m} : Finset ℕ), (d : ℝ) := by simp
    _ ≤ ∑ d ∈ m.divisors, (d : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          rw [Finset.mem_singleton] at ha; subst ha; exact hmem
        · intro d _ _; exact_mod_cast Nat.zero_le d

/-- Per-entry lower bound on `Pker n k`: jump `n−k` with `σ(n−k) ≥ J` and `√n − √k ≤ T` gives
`Pker n k ≥ J·e^{−CT}/(2n)`. -/
lemma Pker_lower {n k : ℕ} {J T : ℝ} (hk1 : 1 ≤ k) (hkn : k < n)
    (hkm : kernelMass n ≤ 2) (hkm0 : 0 < kernelMass n) (hJ0 : 0 ≤ J)
    (hJ : J ≤ ((n - k : ℕ) : ℝ)) (hT : Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ) ≤ T) :
    J * Real.exp (-C * T) / (2 * (n : ℝ)) ≤ Pker n k := by
  have hCpos := C_pos
  have hnk : n - (n - k) = k := Nat.sub_sub_self hkn.le
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le hk1 hkn.le)
  have hsig : J ≤ Sigma.sigmaR (n - k) := le_trans hJ (sigmaR_ge_self (by omega))
  have hexpr : Pker n k
      = Sigma.sigmaR (n - k) * Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ)))
          / ((k : ℝ) * kernelMass n) := by
    unfold Pker
    rw [if_pos ⟨hk1, hkn⟩]
    unfold erdosWeight
    rw [hnk]
    ring
  rw [hexpr]
  have hexp_le : Real.exp (-C * T)
      ≤ Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith [hT, hCpos])
  have hnum : J * Real.exp (-C * T)
      ≤ Sigma.sigmaR (n - k) * Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ))) :=
    mul_le_mul hsig hexp_le (Real.exp_pos _).le (le_trans hJ0 hsig)
  have hden : (k : ℝ) * kernelMass n ≤ 2 * (n : ℝ) := by
    have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn.le
    nlinarith [this, hkm, hkm0, hn0]
  have hden0 : (0 : ℝ) < (k : ℝ) * kernelMass n := mul_pos hk0 hkm0
  rw [div_le_div_iff₀ (mul_pos two_pos hn0) hden0]
  exact mul_le_mul hnum hden hden0.le (mul_nonneg (sigmaR_nonneg _) (Real.exp_pos _).le)

/-- `√n − √k ≤ (n − k)/√n` for `1 ≤ k ≤ n`. -/
lemma sqrt_sub_le {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ) ≤ ((n : ℝ) - (k : ℝ)) / Real.sqrt (n : ℝ) := by
  have hn0 : (0 : ℝ) < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast lt_of_lt_of_le hk1 hkn)
  rw [le_div_iff₀ hn0]
  have hsn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hsk : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
  have hkle : Real.sqrt (k : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hkn)
  nlinarith [hsn, hsk, hkle, Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg (n : ℝ)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Concrete `v0`: single-chain jump-window mass for the Erdős kernel (renewal route B)

Builds toward the positive local-variance input `v0 > 0`.  `Pker_subwindow_mass` lower-bounds the
single-chain `Pker x ·` mass on a jump sub-window `[a, b] ⊆ [⌊√x⌋, 2⌊√x⌋]` via the banked per-term
`Pker_lower`.  Splitting the window into a LOW and a HIGH jump sub-window gives two separated
ρ-decrement clumps, which `product_locVar_ge` (VarianceLower) turns into `v0 > 0`.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Single-chain mass on a jump sub-window `[a,b] ⊆ [s, 2s]` (`s = ⌊√x⌋`), via `Pker_lower`:
each term is `≥ a·e^{-2C}/(2x)`, and there are `b−a+1` of them. -/
lemma Pker_subwindow_mass {x : ℕ} (hx16 : 16 ≤ x)
    (hkmx : kernelMass x ≤ 2) (hkmx0 : 0 < kernelMass x)
    {a b : ℕ} (ha : Nat.sqrt x ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2 * Nat.sqrt x) :
    ((b - a + 1 : ℕ) : ℝ) * ((a : ℝ) * Real.exp (-C * 2) / (2 * (x:ℝ)))
      ≤ ∑ k ∈ Finset.Icc (x - b) (x - a), Pker x k := by
  have hCpos := C_pos
  set s := Nat.sqrt x with hs
  have hs4 : 4 ≤ s := by
    rw [hs]; calc 4 = Nat.sqrt 16 := by norm_num
      _ ≤ Nat.sqrt x := Nat.sqrt_le_sqrt hx16
  have hssx : s * s ≤ x := by rw [hs, ← pow_two]; exact Nat.sqrt_le' x
  have h2sx : 2 * s ≤ x := by nlinarith [hssx, hs4]
  have h2s1x : 2 * s + 1 ≤ x := by nlinarith [hssx, hs4]
  have hbx : b ≤ x := le_trans hb2 h2sx
  have hax : a ≤ x := le_trans hab hbx
  have ha1 : 1 ≤ a := le_trans (by omega) ha
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hsqrtx : (0 : ℝ) < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have hsx2 : (s : ℝ) * (s : ℝ) ≤ (x : ℝ) := by exact_mod_cast hssx
  have hsle_sqrt : (s : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [show (s : ℝ) = Real.sqrt ((s : ℝ) * (s : ℝ)) from (Real.sqrt_mul_self (by positivity)).symm]
    exact Real.sqrt_le_sqrt hsx2
  -- per-term lower bound, uniform over the window
  have hperterm : ∀ k ∈ Finset.Icc (x - b) (x - a),
      (a : ℝ) * Real.exp (-C * 2) / (2 * (x:ℝ)) ≤ Pker x k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1', hk2'⟩ := hk
    have hk_lt_x : k < x := by omega
    have hk_ge1 : 1 ≤ k := by omega
    have hxk_cast : ((x - k : ℕ) : ℝ) = (x : ℝ) - (k : ℝ) := by rw [Nat.cast_sub hk_lt_x.le]
    -- jump bounds: a ≤ x - k ≤ b
    have hjlo : a ≤ x - k := by omega
    have hjhi : x - k ≤ b := by omega
    -- J = a ≤ (x-k)
    have hJ : (a : ℝ) ≤ ((x - k : ℕ) : ℝ) := by exact_mod_cast hjlo
    -- T = 2 : √x − √k ≤ 2
    have hT : Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ) ≤ 2 := by
      refine le_trans (sqrt_sub_le hk_ge1 hk_lt_x.le) ?_
      rw [div_le_iff₀ hsqrtx]
      have hxk2s : ((x : ℝ) - (k : ℝ)) ≤ 2 * (s : ℝ) := by
        rw [← hxk_cast]; exact_mod_cast le_trans hjhi hb2
      nlinarith [hxk2s, hsle_sqrt, hsqrtx]
    exact Pker_lower hk_ge1 hk_lt_x hkmx hkmx0 (by positivity) hJ hT
  -- sum ≥ card • perterm
  have hcard : (Finset.Icc (x - b) (x - a)).card = b - a + 1 := by
    rw [Nat.card_Icc]
    omega
  calc ((b - a + 1 : ℕ) : ℝ) * ((a : ℝ) * Real.exp (-C * 2) / (2 * (x:ℝ)))
      = ((Finset.Icc (x - b) (x - a)).card : ℝ) * ((a : ℝ) * Real.exp (-C * 2) / (2 * (x:ℝ))) := by
        rw [hcard]
    _ ≤ ∑ k ∈ Finset.Icc (x - b) (x - a), Pker x k := by
        rw [← nsmul_eq_mul]
        exact Finset.card_nsmul_le_sum _ _ _ hperterm

/-- Lower bound on the √-decrement: `√x − √k ≥ (x−k)/(2√x)`. -/
lemma sqrt_decrement_lower {x k : ℕ} (hk : k < x) :
    ((x - k : ℕ) : ℝ) / (2 * Real.sqrt x) ≤ Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ) := by
  have hxk : ((x - k : ℕ) : ℝ) = (x : ℝ) - (k : ℝ) := Nat.cast_sub hk.le
  have hkx : (k : ℝ) ≤ (x : ℝ) := by exact_mod_cast hk.le
  have hsk : Real.sqrt (k : ℝ) ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt hkx
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hsx : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hx0
  rw [hxk, div_le_iff₀ (by positivity)]
  have hid : ((x : ℝ) - (k : ℝ))
      = (Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ)) * (Real.sqrt (x : ℝ) + Real.sqrt (k : ℝ)) := by
    have h1 : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith [h1, h2]
  rw [hid]
  exact mul_le_mul_of_nonneg_left (by linarith [hsk]) (by linarith [hsk])

/-- `⌊√x⌋ ≥ (4/5)√x` for `x ≥ 25`. -/
lemma sqrt_floor_lower {x : ℕ} (hx : 25 ≤ x) :
    (4 : ℝ) / 5 * Real.sqrt (x : ℝ) ≤ (Nat.sqrt x : ℝ) := by
  have hlt : Real.sqrt (x : ℝ) < (Nat.sqrt x : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity), sq]
    exact_mod_cast Nat.lt_succ_sqrt x
  have h5 : (5 : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [show (5 : ℝ) = Real.sqrt 25 by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hx)
  linarith

/-- `s² ≥ (16/25)x` for `x ≥ 25` (from `s ≥ (4/5)√x`). -/
lemma sq_floor_lower {x : ℕ} (hx : 25 ≤ x) :
    (16 : ℝ) / 25 * (x : ℝ) ≤ (Nat.sqrt x : ℝ) ^ 2 := by
  have h := sqrt_floor_lower hx
  have hsq : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) := Real.sq_sqrt (by positivity)
  nlinarith [h, hsq, Real.sqrt_nonneg (x : ℝ), (Nat.cast_nonneg (Nat.sqrt x) : (0:ℝ) ≤ (Nat.sqrt x : ℝ))]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
theorem solution {x : ℕ} (hx : 100 ≤ x) (hkmx : kernelMass x ≤ 2) (hkmx0 : 0 < kernelMass x) :
    (Real.exp (-C * 2) / 13
        ≤ ∑ a ∈ Finset.Icc (x - 2 * Nat.sqrt x) (x - 7 * Nat.sqrt x / 4), Pker x a)
      ∧ (∀ a ∈ Finset.Icc (x - 2 * Nat.sqrt x) (x - 7 * Nat.sqrt x / 4),
          (21 : ℝ) / 10 ≤ 3 * (Real.sqrt (x : ℝ) - Real.sqrt (a : ℝ))) := by
  have hx25 : 25 ≤ x := by omega
  set s := Nat.sqrt x with hs
  have hs5 : 5 ≤ s := by
    rw [hs]; calc 5 = Nat.sqrt 25 := by norm_num
      _ ≤ Nat.sqrt x := Nat.sqrt_le_sqrt hx25
  have hss : s * s ≤ x := by rw [hs]; have h := Nat.sqrt_le' x; rwa [pow_two] at h
  have hsx : 2 * s ≤ x := le_trans (by nlinarith [hs5]) hss
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hsqrtx : (0 : ℝ) < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have hsfloor : (4 : ℝ) / 5 * Real.sqrt (x : ℝ) ≤ (s : ℝ) := sqrt_floor_lower hx25
  have hsq16 : (16 : ℝ) / 25 * (x : ℝ) ≤ (s : ℝ) ^ 2 := sq_floor_lower hx25
  -- tight floor bound `√x < s + 1` and `10 ≤ √x` (from `x ≥ 100`)
  have hsx1 : Real.sqrt (x : ℝ) < (s : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity), sq]
    exact_mod_cast Nat.lt_succ_sqrt x
  have hsqrt10 : (10 : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [show (10 : ℝ) = Real.sqrt 100 by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hx)
  -- bounds on window endpoints (Nat)
  have hab : 7 * s / 4 ≤ 2 * s := by omega
  have hsa : s ≤ 7 * s / 4 := by omega
  have hb2 : 2 * s ≤ 2 * s := le_refl _
  refine ⟨?_, ?_⟩
  · -- mass
    have hmass := Pker_subwindow_mass (x := x) (by omega) hkmx hkmx0 hsa hab hb2
    refine le_trans ?_ hmass
    have hexp : 0 < Real.exp (-C * 2) := Real.exp_pos _
    have hwidth : (s : ℝ) ≤ 4 * ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) := by
      have : s ≤ 4 * (2 * s - 7 * s / 4 + 1) := by omega
      exact_mod_cast this
    have ha7 : (s : ℝ) ≤ ((7 * s / 4 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : s ≤ 7 * s / 4)
    have hWnn : (0 : ℝ) ≤ ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have ha7nn : (0 : ℝ) ≤ ((7 * s / 4 : ℕ) : ℝ) := Nat.cast_nonneg _
    -- key: 2x ≤ 13·W·(7s/4)
    have hprod : (s : ℝ) / 4 * (s : ℝ)
        ≤ ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) * ((7 * s / 4 : ℕ) : ℝ) :=
      mul_le_mul (by linarith [hwidth]) ha7 (by positivity) hWnn
    have key : 2 * (x : ℝ) ≤ 13 * (((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) * ((7 * s / 4 : ℕ) : ℝ)) := by
      nlinarith [hprod, hsq16, hxpos]
    show Real.exp (-C * 2) / 13 ≤
      ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) * (((7 * s / 4 : ℕ) : ℝ) * Real.exp (-C * 2) / (2 * (x : ℝ)))
    have hLHSeq : ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ)
        * (((7 * s / 4 : ℕ) : ℝ) * Real.exp (-C * 2) / (2 * (x : ℝ)))
        = ((2 * s - 7 * s / 4 + 1 : ℕ) : ℝ) * ((7 * s / 4 : ℕ) : ℝ) * Real.exp (-C * 2)
            / (2 * (x : ℝ)) := by ring
    rw [hLHSeq, le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hxpos),
        div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 13)]
    nlinarith [mul_le_mul_of_nonneg_left key hexp.le, hexp]
  · -- decrement ≥ 21/10
    intro a ha
    rw [Finset.mem_Icc] at ha
    have haxlt : a < x := by omega
    have hjump : 7 * s / 4 ≤ x - a := by omega
    have hjr : ((7 * s / 4 : ℕ) : ℝ) ≤ ((x - a : ℕ) : ℝ) := by exact_mod_cast hjump
    have hlow := sqrt_decrement_lower (x := x) (k := a) haxlt
    -- √x − √a ≥ (x−a)/(2√x); and 4(x−a) ≥ 7s−3 > 7√x−10 ≥ 2.8√x (since √x ≥ 10) ⟹ (x−a) ≥ 0.7·2√x
    have hbound : (7 : ℝ) / 10 ≤ Real.sqrt (x : ℝ) - Real.sqrt (a : ℝ) := by
      have hge : ((x - a : ℕ) : ℝ) / (2 * Real.sqrt (x : ℝ)) ≤ Real.sqrt (x : ℝ) - Real.sqrt (a : ℝ) :=
        hlow
      -- nat floor fact `7s ≤ 4(x−a) + 3`, cast to ℝ
      have hnat : 7 * s ≤ 4 * (x - a) + 3 := by omega
      have hnatR : 7 * (s : ℝ) ≤ 4 * ((x - a : ℕ) : ℝ) + 3 := by exact_mod_cast hnat
      have hnum : (7 : ℝ) / 10 * (2 * Real.sqrt (x : ℝ)) ≤ ((x - a : ℕ) : ℝ) := by
        nlinarith [hnatR, hsx1, hsqrt10]
      have h710 : (7 : ℝ) / 10 ≤ ((x - a : ℕ) : ℝ) / (2 * Real.sqrt (x : ℝ)) :=
        (le_div_iff₀ (by positivity)).mpr hnum
      linarith [h710, hge]
    linarith [hbound]
