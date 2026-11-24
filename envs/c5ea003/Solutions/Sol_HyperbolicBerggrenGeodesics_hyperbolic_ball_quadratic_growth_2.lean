-- Prove2me | solution 2 for HyperbolicBerggrenGeodesics.hyperbolic_ball_quadratic_growth
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:41.04393+00:00
-- url     : https://prove2.me/submissions/4211083b-3b6c-481f-a923-e20ad59149b1

-- Thm stub generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics

/-!
# Hyperbolic–Pythagorean Geodesics, cycle III: quadratic ball growth

The first cycle proved that the hyperbolic ball of radius `R` around `i` contains at least
`e^{R-2} - 1` Berggren nodes, and conjectured (sub-conjecture **C1-lite**) the true order
`e^{2R}`: the number of nodes should grow like the *hypotenuse*, not like its square root.

This file proves that conjecture.  The obstruction is arithmetic, not geometric: one has to
produce quadratically many *coprime* pairs of opposite parity, which requires a sieve.

## Main results

* `card_multiples_Ioc` : the exact count of multiples of `k` in an interval `(a, b]`.
* `sum_inv_sq_odd`, `sum_inv_odd` : two telescoping estimates,
  `∑_{i<n} 1/(2i+3)² ≤ 1/4` and `∑_{i<n} 1/(2i+3) ≤ √(2n+1) - 1`.
* `card_seedBox_lower` : **the sieve bound.**  For `K ≥ 256` the box
  `{m even, 2K < m ≤ 4K} × {n odd, 1 ≤ n ≤ 2K}` contains at least `K²/4` Euclid seeds.
* `hyperbolic_ball_quadratic_growth` : **C1-lite, closed.**  For every `K ≥ 256` the
  hyperbolic ball of radius `R = log K + 2` around the base point contains at least
  `e^{2R}/300` distinct Berggren nodes.  Since every node with hypotenuse `c` sits at
  distance `≈ ½ log c`, this is the true order of growth, and it shows definitively that
  geodesic search through the Berggren tree cannot beat exhaustive search: the ball that
  is guaranteed to contain a colliding pair for `N` already contains `≍ N` nodes.
-/

open HyperbolicBerggrenGeodesics

open Real UpperHalfPlane

noncomputable section

/-! ## Part A. Counting multiples -/



/-! ## Part B. Two telescoping estimates -/



/-! ## Part C. The sieve -/












/-! ## Part D. From the sieve to a quadratic lower bound -/



/-! ## Part E. Quadratic volume growth of hyperbolic balls (C1-lite, closed) -/

open Real
open UpperHalfPlane
open Real UpperHalfPlane
namespace HyperbolicBerggrenGeodesics

theorem euclidTriple_pythagorean (m n : ℤ) :
    (euclidTriple m n).1 ^ 2 + (euclidTriple m n).2.1 ^ 2 = (euclidTriple m n).2.2 ^ 2 := by
  simp only [euclidTriple]; ring

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem bStepL_triple (m n : ℤ) : bStepL (euclidTriple m n) = euclidTriple (2 * m - n) m := by
  simp only [bStepL, euclidTriple, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem bStepM_triple (m n : ℤ) : bStepM (euclidTriple m n) = euclidTriple (2 * m + n) m := by
  simp only [bStepM, euclidTriple, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem bStepR_triple (m n : ℤ) : bStepR (euclidTriple m n) = euclidTriple (m + 2 * n) n := by
  simp only [bStepR, euclidTriple, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem isSeed_root : IsSeed 2 1 := ⟨one_pos, one_lt_two, by decide, by decide⟩

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem coprime_of_gcd_dvd {a b n : ℕ} (hb : Nat.Coprime b n) (h : Nat.gcd a b ∣ n) :
    Nat.Coprime a b :=
  Nat.eq_one_of_dvd_one (hb ▸ Nat.dvd_gcd (Nat.gcd_dvd_right a b) h)

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem seedL_isSeed {m n : ℕ} (h : IsSeed m n) : IsSeed (seedL (m, n)).1 (seedL (m, n)).2 := by
  obtain ⟨hn, hlt, hc, hp⟩ := h
  refine ⟨lt_trans hn hlt, by simp only [seedL]; omega, ?_, by simp only [seedL]; omega⟩
  simp only [seedL]
  refine HyperbolicBerggrenGeodesics.coprime_of_gcd_dvd hc ?_
  have h1 : Nat.gcd (2 * m - n) m ∣ 2 * m - n := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (2 * m - n) m ∣ m := Nat.gcd_dvd_right _ _
  simpa [show 2 * m - (2 * m - n) = n from by omega] using
    Nat.dvd_sub (Dvd.dvd.mul_left h2 2) h1

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem seedM_isSeed {m n : ℕ} (h : IsSeed m n) : IsSeed (seedM (m, n)).1 (seedM (m, n)).2 := by
  obtain ⟨hn, hlt, hc, hp⟩ := h
  refine ⟨lt_trans hn hlt, by simp only [seedM]; omega, ?_, by simp only [seedM]; omega⟩
  simp only [seedM]
  refine HyperbolicBerggrenGeodesics.coprime_of_gcd_dvd hc ?_
  have h1 : Nat.gcd (2 * m + n) m ∣ 2 * m + n := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (2 * m + n) m ∣ m := Nat.gcd_dvd_right _ _
  simpa [show 2 * m + n - 2 * m = n from by omega] using
    Nat.dvd_sub h1 (Dvd.dvd.mul_left h2 2)

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem seedR_isSeed {m n : ℕ} (h : IsSeed m n) : IsSeed (seedR (m, n)).1 (seedR (m, n)).2 := by
  obtain ⟨hn, hlt, hc, hp⟩ := h
  refine ⟨hn, by simp only [seedR]; omega, ?_, by simp only [seedR]; omega⟩
  simp only [seedR]
  refine HyperbolicBerggrenGeodesics.coprime_of_gcd_dvd hc.symm ?_
  have h1 : Nat.gcd (m + 2 * n) n ∣ m + 2 * n := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (m + 2 * n) n ∣ n := Nat.gcd_dvd_right _ _
  simpa [show m + 2 * n - 2 * n = m from by omega] using
    Nat.dvd_sub h1 (Dvd.dvd.mul_left h2 2)

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

@[simp] theorem hpoint_re (m n : ℕ) (hm : 0 < m) : (hpoint m n hm).re = (n : ℝ) / m := rfl

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

@[simp] theorem hpoint_im (m n : ℕ) (hm : 0 < m) : (hpoint m n hm).im = 1 / (m : ℝ) := rfl

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem cosh_dist_hpoint_I (m n : ℕ) (hm : 0 < m) :
    Real.cosh (dist (hpoint m n hm) UpperHalfPlane.I) = ((m : ℝ) ^ 2 + (n : ℝ) ^ 2 + 1) / (2 * m) := by
  have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [UpperHalfPlane.cosh_dist']
  simp only [HyperbolicBerggrenGeodesics.hpoint_re, HyperbolicBerggrenGeodesics.hpoint_im, UpperHalfPlane.I_re, UpperHalfPlane.I_im]
  field_simp
  ring

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem log_cosh_sandwich {d : ℝ} (hd : 0 ≤ d) :
    Real.log (Real.cosh d) ≤ d ∧ d ≤ Real.log (2 * Real.cosh d) := by
  have hcpos : 0 < Real.cosh d := Real.cosh_pos d
  have hexp : Real.cosh d + Real.sinh d = Real.exp d := Real.cosh_add_sinh d
  have hs : 0 ≤ Real.sinh d := Real.sinh_nonneg_iff.mpr hd
  have hsc : Real.sinh d ≤ Real.cosh d := (Real.sinh_lt_cosh d).le
  constructor
  · have h1 : Real.cosh d ≤ Real.exp d := by linarith
    calc Real.log (Real.cosh d) ≤ Real.log (Real.exp d) := Real.log_le_log hcpos h1
      _ = d := Real.log_exp d
  · have h2 : Real.exp d ≤ 2 * Real.cosh d := by linarith
    calc d = Real.log (Real.exp d) := (Real.log_exp d).symm
      _ ≤ Real.log (2 * Real.cosh d) := Real.log_le_log (Real.exp_pos d) h2

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem hyperbolic_dist_eq_half_log_hypotenuse {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    |dist (hpoint m n (lt_trans hn hnm)) UpperHalfPlane.I -
        (1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)| ≤ Real.log 2 := by
  set hm : 0 < m := lt_trans hn hnm with hmdef
  set d := dist (hpoint m n hm) UpperHalfPlane.I with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `m² ≥ n² + 1` because `n < m` are naturals
  have hsq : (n : ℝ) ^ 2 + 1 ≤ (m : ℝ) ^ 2 := by
    have : n ^ 2 + 1 ≤ m ^ 2 := by nlinarith [hnm, hn]
    exact_mod_cast this
  set c : ℝ := (m : ℝ) ^ 2 + (n : ℝ) ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hc1 : 1 ≤ c := by nlinarith
  have hA : Real.cosh d = (c + 1) / (2 * m) := by
    rw [hd, HyperbolicBerggrenGeodesics.cosh_dist_hpoint_I]
  set A : ℝ := (c + 1) / (2 * m) with hAdef
  have hApos : 0 < A := by positivity
  obtain ⟨hlow, hhigh⟩ := HyperbolicBerggrenGeodesics.log_cosh_sandwich hd0
  rw [hA] at hlow hhigh
  -- Upper bound
  have hup : d ≤ Real.log 2 + (1 / 2) * Real.log c := by
    have key : (2 * A) ^ 2 ≤ 4 * c := by
      rw [hAdef]
      have h2m : c + 1 ≤ 2 * (m : ℝ) ^ 2 := by nlinarith
      have : ((c + 1) / (m : ℝ)) ^ 2 ≤ 4 * c := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (c + 1), sq_nonneg ((m : ℝ))]
      calc (2 * ((c + 1) / (2 * (m : ℝ)))) ^ 2 = ((c + 1) / (m : ℝ)) ^ 2 := by
            field_simp
        _ ≤ 4 * c := this
    have h1 : Real.log (2 * A) ≤ Real.log (4 * c) := Real.log_le_log (by positivity) (by nlinarith)
    have h2 : 2 * Real.log (2 * A) = Real.log ((2 * A) ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    have h3 : Real.log ((2 * A) ^ 2) ≤ Real.log (4 * c) :=
      Real.log_le_log (by positivity) key
    have h4 : Real.log (4 * c) = 2 * Real.log 2 + Real.log c := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hcpos),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have : 2 * d ≤ 2 * Real.log 2 + Real.log c := by
      calc 2 * d ≤ 2 * Real.log (2 * A) := by linarith
        _ = Real.log ((2 * A) ^ 2) := h2
        _ ≤ Real.log (4 * c) := h3
        _ = 2 * Real.log 2 + Real.log c := h4
    linarith
  -- Lower bound
  have hlo : Real.log 2 + d ≥ (1 / 2) * Real.log c := by
    have hm2 : (m : ℝ) ^ 2 ≤ c := by nlinarith
    have key : c / 4 ≤ A ^ 2 := by
      rw [hAdef, div_pow, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c - 1), mul_pos hcpos hcpos]
    have h2 : 2 * Real.log A = Real.log (A ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    have h3 : Real.log (c / 4) ≤ Real.log (A ^ 2) := Real.log_le_log (by positivity) key
    have h4 : Real.log (c / 4) = Real.log c - 2 * Real.log 2 := by
      rw [Real.log_div (ne_of_gt hcpos) (by norm_num),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have : Real.log c - 2 * Real.log 2 ≤ 2 * d := by
      calc Real.log c - 2 * Real.log 2 = Real.log (c / 4) := h4.symm
        _ ≤ Real.log (A ^ 2) := h3
        _ = 2 * Real.log A := h2.symm
        _ ≤ 2 * d := by linarith
    linarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem spine_eq (k : ℕ) : spine k = (k + 2, k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hrec : spine (k + 1) = seedL (spine k) := rfl
    rw [hrec, ih]
    have h1 : 2 * (k + 2) - (k + 1) = k + 1 + 2 := by omega
    show (2 * (k + 2) - (k + 1), k + 2) = (k + 1 + 2, k + 1 + 1)
    rw [h1]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem spine_isSeed (k : ℕ) : IsSeed (spine k).1 (spine k).2 := by
  rw [HyperbolicBerggrenGeodesics.spine_eq]
  refine ⟨by omega, by omega, ?_, by omega⟩
  rw [show k + 2 = (k + 1) + 1 from rfl, Nat.coprime_self_add_left]
  exact Nat.coprime_one_left _

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem spine_hypotenuse (k : ℕ) : (spine k).1 ^ 2 + (spine k).2 ^ 2 = 2 * k ^ 2 + 6 * k + 5 := by
  rw [HyperbolicBerggrenGeodesics.spine_eq]; ring

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem spinePoint_im (k : ℕ) : (spinePoint k).im = 1 / ((k : ℝ) + 2) := by
  simp [spinePoint]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem spinePoint_injective : Function.Injective spinePoint := by
  intro i j hij
  have h : (1 : ℝ) / ((i : ℝ) + 2) = 1 / ((j : ℝ) + 2) := by
    rw [← HyperbolicBerggrenGeodesics.spinePoint_im, ← HyperbolicBerggrenGeodesics.spinePoint_im, hij]
  have hi : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  have hj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have : (i : ℝ) = (j : ℝ) := by
    field_simp at h; linarith
  exact_mod_cast this

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem spine_dist_le (k : ℕ) :
    dist (spinePoint k) UpperHalfPlane.I ≤ Real.log ((k : ℝ) + 2) + 2 := by
  have hb := HyperbolicBerggrenGeodesics.hyperbolic_dist_eq_half_log_hypotenuse (m := k + 2) (n := k + 1)
    (by omega) (by omega)
  rw [abs_le] at hb
  have hc : (((k : ℕ) + 2 : ℕ) : ℝ) ^ 2 + (((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * ((k : ℝ) + 2) ^ 2 := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast; nlinarith
  have hcpos : (0 : ℝ) < (((k : ℕ) + 2 : ℕ) : ℝ) ^ 2 + (((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast; positivity
  have hlog : Real.log ((((k : ℕ) + 2 : ℕ) : ℝ) ^ 2 + (((k : ℕ) + 1 : ℕ) : ℝ) ^ 2)
      ≤ Real.log 2 + 2 * Real.log ((k : ℝ) + 2) := by
    have h1 := Real.log_le_log hcpos hc
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    push_cast at h1 ⊢
    linarith
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have : dist (spinePoint k) UpperHalfPlane.I ≤
      Real.log 2 + (1 / 2) * (Real.log 2 + 2 * Real.log ((k : ℝ) + 2)) := by
    have := hb.2
    simp only [spinePoint] at *
    linarith
  linarith

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem depth_not_bounded_by_distance (C : ℝ) (hC : 0 ≤ C) :
    ∃ k : ℕ, C * dist (spinePoint k) UpperHalfPlane.I < k := by
  set K : ℕ := ⌈(2 * C + 3) ^ 2⌉₊ with hK
  refine ⟨K, ?_⟩
  have hKge : (2 * C + 3) ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  set t : ℝ := Real.sqrt ((K : ℝ) + 2) with ht
  have ht0 : 0 ≤ (K : ℝ) + 2 := by positivity
  have ht2 : t ^ 2 = (K : ℝ) + 2 := Real.sq_sqrt ht0
  have htpos : 0 < t := Real.sqrt_pos.2 (by positivity)
  have htge : 2 * C + 3 ≤ t := by
    rw [ht]
    rw [show (2 * C + 3) = Real.sqrt ((2 * C + 3) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  -- `log (K+2) ≤ 2 (t - 1)`
  have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
  have hlogK : Real.log ((K : ℝ) + 2) ≤ 2 * t - 2 := by
    have : Real.log ((K : ℝ) + 2) = 2 * Real.log t := by
      rw [← ht2, Real.log_pow]; push_cast; ring
    rw [this]; linarith
  have hd := HyperbolicBerggrenGeodesics.spine_dist_le K
  have hstep : C * dist (spinePoint K) UpperHalfPlane.I ≤ C * (Real.log ((K : ℝ) + 2) + 2) :=
    mul_le_mul_of_nonneg_left hd hC
  have h2 : C * (Real.log ((K : ℝ) + 2) + 2) ≤ 2 * C * t := by nlinarith
  have h3 : 2 * C * t < (K : ℝ) := by nlinarith
  linarith

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem hyperbolic_ball_volume_growth (K : ℕ) :
    ∃ (R : ℝ) (S : Finset ℍ), R = Real.log ((K : ℝ) + 2) + 2 ∧
      (S.card : ℝ) = Real.exp (R - 2) - 1 ∧
      ∀ z ∈ S, dist z UpperHalfPlane.I ≤ R := by
  classical
  refine ⟨Real.log ((K : ℝ) + 2) + 2, (Finset.range (K + 1)).image spinePoint, rfl, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ HyperbolicBerggrenGeodesics.spinePoint_injective, Finset.card_range]
    have : Real.log ((K : ℝ) + 2) + 2 - 2 = Real.log ((K : ℝ) + 2) := by ring
    rw [this, Real.exp_log (by positivity)]
    push_cast; ring
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
    have hjK : (j : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    refine le_trans (HyperbolicBerggrenGeodesics.spine_dist_le j) ?_
    have : Real.log ((j : ℝ) + 2) ≤ Real.log ((K : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem dist_le_pathLength (z : ℕ → ℍ) (k : ℕ) : dist (z 0) (z k) ≤ pathLength z k := by
  induction k with
  | zero => simp [pathLength]
  | succ k ih =>
    rw [pathLength, Finset.sum_range_succ, ← pathLength]
    exact le_trans (dist_triangle (z 0) (z k) (z (k + 1))) (by linarith)

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem sq_pathLength_le (z : ℕ → ℍ) (k : ℕ) :
    pathLength z k ^ 2 ≤ (k : ℝ) * pathEnergy z k := by
  have := sq_sum_le_card_mul_sum_sq (s := Finset.range k)
    (f := fun i => dist (z i) (z (i + 1)))
  simpa [pathLength, pathEnergy] using this

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem geodesic_energy_lower_bound (z : ℕ → ℍ) (k : ℕ) (hk : 0 < k) :
    dist (z 0) (z k) ^ 2 / (k : ℝ) ≤ pathEnergy z k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : dist (z 0) (z k) ^ 2 ≤ pathLength z k ^ 2 := by
    have h0 : 0 ≤ dist (z 0) (z k) := dist_nonneg
    have := HyperbolicBerggrenGeodesics.dist_le_pathLength z k
    nlinarith
  have h2 := HyperbolicBerggrenGeodesics.sq_pathLength_le z k
  rw [div_le_iff₀ hkR]
  nlinarith

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem berggren_trajectory_energy_bound {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    (z : ℕ → ℍ) (k : ℕ) (hk : 0 < k)
    (h0 : z 0 = UpperHalfPlane.I) (hkz : z k = hpoint m n (lt_trans hn hnm)) :
    ((1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) - Real.log 2) ^ 2 / (k : ℝ)
      ≤ pathEnergy z k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hb := HyperbolicBerggrenGeodesics.hyperbolic_dist_eq_half_log_hypotenuse hn hnm
  rw [abs_le] at hb
  -- the seed forces `m ≥ 2`, hence `c ≥ 5 > 4`, hence `½ log c ≥ log 2`
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc4 : (4 : ℝ) ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by nlinarith
  have hL : 0 ≤ (1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) - Real.log 2 := by
    have h1 : Real.log 4 ≤ Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) :=
      Real.log_le_log (by norm_num) hc4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hdist : (1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) - Real.log 2
      ≤ dist (z 0) (z k) := by
    rw [h0, hkz, dist_comm]
    linarith [hb.1]
  have hsq : ((1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) - Real.log 2) ^ 2
      ≤ dist (z 0) (z k) ^ 2 := by nlinarith
  have := HyperbolicBerggrenGeodesics.geodesic_energy_lower_bound z k hk
  calc ((1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) - Real.log 2) ^ 2 / (k : ℝ)
      ≤ dist (z 0) (z k) ^ 2 / (k : ℝ) := by
        gcongr
    _ ≤ pathEnergy z k := this

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem lt_of_sq_add_sq_eq {x y n : ℤ} (h : x ^ 2 + y ^ 2 = n ^ 2) (hy : y ≠ 0)
    (hx : 0 ≤ x) (hn : 0 ≤ n) : x < n := by
  have hy2 : 0 < y ^ 2 := pow_two_pos_of_ne_zero hy
  nlinarith

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem repr_dot_lt {a b c d N : ℕ} (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N)
    (hne : a * d ≠ b * c) : a * c + b * d < N := by
  have key : ((a : ℤ) * c + b * d) ^ 2 + ((a : ℤ) * d - b * c) ^ 2 = (N : ℤ) ^ 2 := by
    have e1 : ((a : ℤ)) ^ 2 + (b : ℤ) ^ 2 = (N : ℤ) := by exact_mod_cast h1
    have e2 : ((c : ℤ)) ^ 2 + (d : ℤ) ^ 2 = (N : ℤ) := by exact_mod_cast h2
    calc ((a : ℤ) * c + b * d) ^ 2 + ((a : ℤ) * d - b * c) ^ 2
        = ((a : ℤ) ^ 2 + b ^ 2) * ((c : ℤ) ^ 2 + d ^ 2) := by ring
      _ = (N : ℤ) ^ 2 := by rw [e1, e2]; ring
  have hy : ((a : ℤ) * d - b * c) ≠ 0 := by
    intro hcon
    exact hne (by exact_mod_cast sub_eq_zero.1 hcon)
  have := HyperbolicBerggrenGeodesics.lt_of_sq_add_sq_eq key hy (by positivity) (by positivity)
  exact_mod_cast this

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem euler_two_representations_factor {a b c d N : ℕ} (ha : 0 < a)
    (hc : 0 < c) (hd : 0 < d) (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N)
    (hne1 : a * d ≠ b * c) (hne2 : a * c ≠ b * d) :
    1 < Nat.gcd N (a * c + b * d) ∧ Nat.gcd N (a * c + b * d) < N := by
  set P := a * c + b * d with hP
  set Q := a * d + b * c with hQ
  have hNpos : 0 < N := by nlinarith
  have hPpos : 0 < P := Nat.add_pos_left (Nat.mul_pos ha hc) _
  have hQpos : 0 < Q := Nat.add_pos_left (Nat.mul_pos ha hd) _
  have hPlt : P < N := HyperbolicBerggrenGeodesics.repr_dot_lt h1 h2 hne1
  have hQlt : Q < N := HyperbolicBerggrenGeodesics.repr_dot_lt h1 (by omega : d ^ 2 + c ^ 2 = N) hne2
  have hPQ : P * Q = N * (c * d + a * b) := by
    have hexp : P * Q = (a ^ 2 + b ^ 2) * (c * d) + (c ^ 2 + d ^ 2) * (a * b) := by
      rw [hP, hQ]; ring
    rw [h1, h2] at hexp
    rw [hexp]; ring
  have hdvd : N ∣ P * Q := ⟨c * d + a * b, hPQ⟩
  constructor
  · by_contra hcon
    push_neg at hcon
    have hgne : Nat.gcd N P ≠ 0 := by
      simp only [ne_eq, Nat.gcd_eq_zero_iff, not_and]
      omega
    have hcop : Nat.Coprime N P := by
      unfold Nat.Coprime; omega
    have : N ∣ Q := hcop.dvd_of_dvd_mul_left hdvd
    have := Nat.le_of_dvd hQpos this
    omega
  · have hle : Nat.gcd N P ≤ N := Nat.le_of_dvd hNpos (Nat.gcd_dvd_left _ _)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hNP : N ∣ P := h ▸ Nat.gcd_dvd_right N P
      have := Nat.le_of_dvd hPpos hNP
      omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem seed_cross_ne {m₁ n₁ m₂ n₂ : ℕ} (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hne : (m₁, n₁) ≠ (m₂, n₂)) : m₁ * n₂ ≠ n₁ * m₂ := by
  intro hcross
  have hm1 : 0 < m₁ := lt_trans h₁.pos h₁.lt
  have hd1 : m₁ ∣ m₂ := h₁.cop.dvd_of_dvd_mul_left ⟨n₂, hcross.symm⟩
  have hd2 : m₂ ∣ m₁ :=
    h₂.cop.dvd_of_dvd_mul_left ⟨n₁, by rw [mul_comm n₂ m₁, hcross]; exact mul_comm n₁ m₂⟩
  have hm : m₁ = m₂ := Nat.dvd_antisymm hd1 hd2
  subst hm
  have : n₂ = n₁ :=
    Nat.eq_of_mul_eq_mul_left hm1 (by rw [hcross]; exact mul_comm n₁ m₁)
  exact hne (by simp [this])

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem berggren_collision_factors {m₁ n₁ m₂ n₂ N : ℕ} (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hN₁ : m₁ ^ 2 + n₁ ^ 2 = N) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = N) (hne : (m₁, n₁) ≠ (m₂, n₂)) :
    1 < Nat.gcd N (m₁ * m₂ + n₁ * n₂) ∧ Nat.gcd N (m₁ * m₂ + n₁ * n₂) < N := by
  have hm1 : 0 < m₁ := lt_trans h₁.pos h₁.lt
  have hm2 : 0 < m₂ := lt_trans h₂.pos h₂.lt
  refine HyperbolicBerggrenGeodesics.euler_two_representations_factor hm1 hm2 h₂.pos hN₁ hN₂ ?_ ?_
  · exact HyperbolicBerggrenGeodesics.seed_cross_ne h₁ h₂ hne
  · -- `m₁ m₂ > n₁ n₂` because `m > n` in both seeds
    have hlt : n₁ * n₂ < m₁ * m₂ :=
      Nat.mul_lt_mul_of_lt_of_le h₁.lt h₂.lt.le (lt_trans h₂.pos h₂.lt)
    omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem berggren_collision_not_prime {m₁ n₁ m₂ n₂ N : ℕ} (h₁ : IsSeed m₁ n₁)
    (h₂ : IsSeed m₂ n₂) (hN₁ : m₁ ^ 2 + n₁ ^ 2 = N) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = N)
    (hne : (m₁, n₁) ≠ (m₂, n₂)) : ¬ Nat.Prime N := by
  intro hp
  obtain ⟨hlow, hhigh⟩ := berggren_collision_factors h₁ h₂ hN₁ hN₂ hne
  have hdvd : Nat.gcd N (m₁ * m₂ + n₁ * n₂) ∣ N := Nat.gcd_dvd_left _ _
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h | h <;> omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem seed_children_distinct {m n : ℕ} (h : IsSeed m n) :
    seedL (m, n) ≠ seedM (m, n) ∧ seedL (m, n) ≠ seedR (m, n) ∧
      seedM (m, n) ≠ seedR (m, n) := by
  obtain ⟨hn, hlt, -, -⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [seedL, seedM, seedR, ne_eq, Prod.mk.injEq, not_and] <;>
    intro h1 <;> omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem isSeed_eight_one : IsSeed 8 1 := ⟨by norm_num, by norm_num, by decide, by decide⟩

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem isSeed_seven_four : IsSeed 7 4 := ⟨by norm_num, by norm_num, by decide, by decide⟩

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem berggren_collision_65 :
    1 < Nat.gcd 65 (8 * 7 + 1 * 4) ∧ Nat.gcd 65 (8 * 7 + 1 * 4) < 65 :=
  berggren_collision_factors HyperbolicBerggrenGeodesics.isSeed_eight_one HyperbolicBerggrenGeodesics.isSeed_seven_four (by norm_num) (by norm_num)
    (by decide)

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem berggren_collision_65_value : Nat.gcd 65 (8 * 7 + 1 * 4) = 5 := by decide

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem sixtyfive_not_prime : ¬ Nat.Prime 65 :=
  berggren_collision_not_prime HyperbolicBerggrenGeodesics.isSeed_eight_one HyperbolicBerggrenGeodesics.isSeed_seven_four (by norm_num) (by norm_num)
    (by decide)

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem collision_dot_bounds {m₁ n₁ m₂ n₂ N : ℕ} (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hN₁ : m₁ ^ 2 + n₁ ^ 2 = N) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = N) (hne : (m₁, n₁) ≠ (m₂, n₂)) :
    N < 2 * (m₁ * m₂ + n₁ * n₂) ∧ m₁ * m₂ + n₁ * n₂ < N := by
  refine ⟨?_, HyperbolicBerggrenGeodesics.repr_dot_lt hN₁ hN₂ (HyperbolicBerggrenGeodesics.seed_cross_ne h₁ h₂ hne)⟩
  -- `2m₁² > N` and `2m₂² > N` force `(2m₁m₂)² > N²`, hence `2 m₁ m₂ > N`
  have hs1 : n₁ ^ 2 < m₁ ^ 2 := Nat.pow_lt_pow_left h₁.lt (by norm_num)
  have hs2 : n₂ ^ 2 < m₂ ^ 2 := Nat.pow_lt_pow_left h₂.lt (by norm_num)
  have e1 : N < 2 * m₁ ^ 2 := by omega
  have e2 : N < 2 * m₂ ^ 2 := by omega
  have e3 : N * N < (2 * (m₁ * m₂)) * (2 * (m₁ * m₂)) := by nlinarith
  by_contra hcon
  push_neg at hcon
  have e4 : 2 * (m₁ * m₂) ≤ N := le_trans (by nlinarith) hcon
  exact absurd e3 (not_lt.2 (Nat.mul_le_mul e4 e4))

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem collision_dist_close {m₁ n₁ m₂ n₂ N : ℕ} (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hN₁ : m₁ ^ 2 + n₁ ^ 2 = N) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = N) :
    |dist (hpoint m₁ n₁ (lt_trans h₁.pos h₁.lt)) UpperHalfPlane.I -
      dist (hpoint m₂ n₂ (lt_trans h₂.pos h₂.lt)) UpperHalfPlane.I| ≤ 2 * Real.log 2 := by
  have e₁ := HyperbolicBerggrenGeodesics.hyperbolic_dist_eq_half_log_hypotenuse h₁.pos h₁.lt
  have e₂ := HyperbolicBerggrenGeodesics.hyperbolic_dist_eq_half_log_hypotenuse h₂.pos h₂.lt
  rw [abs_le] at e₁ e₂ ⊢
  have hcast : ((m₁ : ℝ) ^ 2 + (n₁ : ℝ) ^ 2) = ((m₂ : ℝ) ^ 2 + (n₂ : ℝ) ^ 2) := by
    have : (m₁ ^ 2 + n₁ ^ 2 : ℕ) = (m₂ ^ 2 + n₂ ^ 2 : ℕ) := by omega
    exact_mod_cast this
  rw [hcast] at e₁
  constructor <;> linarith [e₁.1, e₁.2, e₂.1, e₂.2]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem cosh_half_log {c : ℝ} (hc : 0 < c) :
    Real.cosh ((1 / 2) * Real.log c) = (c + 1) / (2 * Real.sqrt c) := by
  have hsq : Real.sqrt c = Real.exp ((1 / 2) * Real.log c) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hc]
    ring_nf
  have hspos : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hss : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  rw [Real.cosh_eq, ← hsq, Real.exp_neg, ← hsq]
  field_simp
  linarith [hss]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem dist_ge_half_log_hypotenuse {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    (1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤
      dist (hpoint m n (lt_trans hn hnm)) UpperHalfPlane.I := by
  have hm : 0 < m := lt_trans hn hnm
  have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set c : ℝ := (m : ℝ) ^ 2 + (n : ℝ) ^ 2 with hcdef
  have hcpos : 0 < c := by positivity
  set d := dist (hpoint m n hm) UpperHalfPlane.I with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hcosh : Real.cosh d = (c + 1) / (2 * m) := by rw [hd, HyperbolicBerggrenGeodesics.cosh_dist_hpoint_I]
  -- `m ≤ √c`
  have hsq : Real.sqrt c ≥ (m : ℝ) := by
    rw [show (m : ℝ) = Real.sqrt ((m : ℝ) ^ 2) from (Real.sqrt_sq hM.le).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hspos : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
  have hkey : Real.cosh ((1 / 2) * Real.log c) ≤ Real.cosh d := by
    rw [HyperbolicBerggrenGeodesics.cosh_half_log hcpos, hcosh]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith
  have := (Real.cosh_le_cosh).1 hkey
  calc (1 / 2) * Real.log c ≤ |(1 / 2) * Real.log c| := le_abs_self _
    _ ≤ |d| := this
    _ = d := abs_of_nonneg hd0

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem dist_le_half_log_two_hypotenuse {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    dist (hpoint m n (lt_trans hn hnm)) UpperHalfPlane.I ≤
      (1 / 2) * Real.log (2 * (((m : ℝ) ^ 2 + (n : ℝ) ^ 2) + 1)) := by
  have hm : 0 < m := lt_trans hn hnm
  have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmn : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnm
  set c : ℝ := (m : ℝ) ^ 2 + (n : ℝ) ^ 2 with hcdef
  have hcpos : 0 < c := by positivity
  set d := dist (hpoint m n hm) UpperHalfPlane.I with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hcosh : Real.cosh d = (c + 1) / (2 * m) := by rw [hd, HyperbolicBerggrenGeodesics.cosh_dist_hpoint_I]
  obtain ⟨-, hhigh⟩ := HyperbolicBerggrenGeodesics.log_cosh_sandwich hd0
  have h2c : 2 * Real.cosh d = (c + 1) / (m : ℝ) := by rw [hcosh]; field_simp
  -- `2 m² ≥ c + 1`, hence `((c+1)/m)² ≤ 2 (c+1)`
  have hm2 : c + 1 ≤ 2 * (m : ℝ) ^ 2 := by nlinarith
  have hkey : ((c + 1) / (m : ℝ)) ^ 2 ≤ 2 * (c + 1) := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have hpos : (0 : ℝ) < (c + 1) / (m : ℝ) := by positivity
  have hlog : Real.log ((c + 1) / (m : ℝ)) ≤ (1 / 2) * Real.log (2 * (c + 1)) := by
    have h1 : Real.log (((c + 1) / (m : ℝ)) ^ 2) ≤ Real.log (2 * (c + 1)) :=
      Real.log_le_log (by positivity) hkey
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  rw [h2c] at hhigh
  linarith

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem trajectory_window {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    0 ≤ dist (hpoint m n (lt_trans hn hnm)) UpperHalfPlane.I -
        (1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ∧
      dist (hpoint m n (lt_trans hn hnm)) UpperHalfPlane.I -
        (1 / 2) * Real.log ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)
        ≤ (1 / 2) * Real.log 2 + 1 / (2 * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) := by
  have hM : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast lt_trans hn hnm
  set c : ℝ := (m : ℝ) ^ 2 + (n : ℝ) ^ 2 with hcdef
  have hcpos : 0 < c := by positivity
  refine ⟨by linarith [HyperbolicBerggrenGeodesics.dist_ge_half_log_hypotenuse hn hnm], ?_⟩
  have hup := HyperbolicBerggrenGeodesics.dist_le_half_log_two_hypotenuse hn hnm
  -- `½ log (2 (c+1)) = ½ log 2 + ½ log c + ½ log ((c+1)/c) ≤ ½ log 2 + ½ log c + 1/(2c)`
  have hsplit : Real.log (2 * (c + 1)) = Real.log 2 + Real.log c + Real.log ((c + 1) / c) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_div (by positivity) (by positivity)]
    ring
  have hlog1 : Real.log ((c + 1) / c) ≤ 1 / c := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (c + 1) / c by positivity)
    have hc : (c + 1) / c - 1 = 1 / c := by
      field_simp
      linarith
    linarith [hc ▸ this]
  rw [hsplit] at hup
  have : (1 : ℝ) / (2 * c) = (1 / 2) * (1 / c) := by
    rw [← div_div, div_eq_mul_one_div]
  linarith

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem hpoint_injective {m₁ n₁ m₂ n₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (h : hpoint m₁ n₁ h₁ = hpoint m₂ n₂ h₂) : m₁ = m₂ ∧ n₁ = n₂ := by
  have hM₁ : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast h₁
  have hM₂ : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast h₂
  have him : (1 : ℝ) / (m₁ : ℝ) = 1 / (m₂ : ℝ) := by
    have := congrArg UpperHalfPlane.im h
    simpa using this
  have hm : (m₁ : ℝ) = (m₂ : ℝ) := by
    field_simp at him; linarith
  have hmnat : m₁ = m₂ := by exact_mod_cast hm
  refine ⟨hmnat, ?_⟩
  have hre : (n₁ : ℝ) / (m₁ : ℝ) = (n₂ : ℝ) / (m₂ : ℝ) := by
    have := congrArg UpperHalfPlane.re h
    simpa using this
  rw [← hm] at hre
  have : (n₁ : ℝ) = (n₂ : ℝ) := by
    field_simp at hre; linarith
  exact_mod_cast this

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem seed_point_injective {m₁ n₁ m₂ n₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (hne : (m₁, n₁) ≠ (m₂, n₂)) : hpoint m₁ n₁ h₁ ≠ hpoint m₂ n₂ h₂ := by
  intro h
  obtain ⟨hm, hn⟩ := HyperbolicBerggrenGeodesics.hpoint_injective h₁ h₂ h
  exact hne (by rw [hm, hn])

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem dist_vertGeodesic (t : ℝ) (k : ℕ) (i j : ℕ) :
    dist (vertGeodesic t k i) (vertGeodesic t k j) = |t * i / k - t * j / k| := by
  have := (UpperHalfPlane.isometry_vertical_line 0).dist_eq (t * i / k) (t * j / k)
  simpa [vertGeodesic, Real.dist_eq] using this

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem dist_vertGeodesic_step {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    dist (vertGeodesic t k j) (vertGeodesic t k (j + 1)) = t / k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [HyperbolicBerggrenGeodesics.dist_vertGeodesic]
  have : t * (j : ℝ) / k - t * ((j : ℕ) + 1 : ℕ) / k = -(t / k) := by
    push_cast; field_simp; ring
  rw [this, abs_neg, abs_of_nonneg (by positivity)]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem dist_vertGeodesic_endpoints {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : 0 < k) :
    dist (vertGeodesic t k 0) (vertGeodesic t k k) = t := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h0 : t * ((0 : ℕ) : ℝ) / (k : ℝ) = 0 := by simp
  have h1 : t * ((k : ℕ) : ℝ) / (k : ℝ) = t := by field_simp
  rw [HyperbolicBerggrenGeodesics.dist_vertGeodesic, h0, h1, zero_sub, abs_neg, abs_of_nonneg ht]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem vertGeodesic_energy {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : 0 < k) :
    pathEnergy (vertGeodesic t k) k = t ^ 2 / k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  unfold pathEnergy
  rw [Finset.sum_congr rfl (fun j _ => by rw [HyperbolicBerggrenGeodesics.dist_vertGeodesic_step ht hk j])]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem energy_lower_bound_sharp {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : 0 < k) :
    ∃ z : ℕ → ℍ, dist (z 0) (z k) = t ∧
      pathEnergy z k = dist (z 0) (z k) ^ 2 / (k : ℝ) := by
  refine ⟨vertGeodesic t k, HyperbolicBerggrenGeodesics.dist_vertGeodesic_endpoints ht hk, ?_⟩
  rw [HyperbolicBerggrenGeodesics.dist_vertGeodesic_endpoints ht hk, HyperbolicBerggrenGeodesics.vertGeodesic_energy ht hk]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem euler_cross_product {a b c d N : ℕ} (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N) :
    (a * c + b * d) * (a * d + b * c) = N * (a * b + c * d) := by
  have hexp : (a * c + b * d) * (a * d + b * c)
      = (a ^ 2 + b ^ 2) * (c * d) + (c ^ 2 + d ^ 2) * (a * b) := by ring
  rw [h1, h2] at hexp
  rw [hexp]; ring

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem sq_mod_two (x : ℕ) : x ^ 2 % 2 = x % 2 := by
  conv_lhs => rw [Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [h]
  · rw [h]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem seed_hypotenuse_odd {m n : ℕ} (h : IsSeed m n) : (m ^ 2 + n ^ 2) % 2 = 1 := by
  have hm := HyperbolicBerggrenGeodesics.sq_mod_two m
  have hn := HyperbolicBerggrenGeodesics.sq_mod_two n
  have hp := h.parity
  omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem collision_gcd_three_eq_one {a b c d N : ℕ} (hodd : N % 2 = 1)
    (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d)
    (h1 : a ^ 2 + b ^ 2 = N) :
    Nat.gcd (Nat.gcd N (a * c + b * d)) (a * d + b * c) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpNP : p ∣ Nat.gcd N (a * c + b * d) := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpN : p ∣ N := hpNP.trans (Nat.gcd_dvd_left _ _)
  have hpP : p ∣ a * c + b * d := hpNP.trans (Nat.gcd_dvd_right _ _)
  have hpQ : p ∣ a * d + b * c := hpd.trans (Nat.gcd_dvd_right _ _)
  -- move to `ℤ`, where the subtraction `a² - b²` makes sense
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hPZ : (p : ℤ) ∣ (a : ℤ) * c + (b : ℤ) * d := by exact_mod_cast Int.natCast_dvd_natCast.2 hpP
  have hQZ : (p : ℤ) ∣ (a : ℤ) * d + (b : ℤ) * c := by exact_mod_cast Int.natCast_dvd_natCast.2 hpQ
  have hNZ : (p : ℤ) ∣ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
    have : ((a ^ 2 + b ^ 2 : ℕ) : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by push_cast; ring
    rw [← this, h1]
    exact Int.natCast_dvd_natCast.2 hpN
  have hc1 : (p : ℤ) ∣ (c : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2) := by
    have hid : (c : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2)
        = (a : ℤ) * ((a : ℤ) * c + (b : ℤ) * d) - (b : ℤ) * ((a : ℤ) * d + (b : ℤ) * c) := by ring
    rw [hid]
    exact dvd_sub (hPZ.mul_left _) (hQZ.mul_left _)
  have hd1 : (p : ℤ) ∣ (d : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2) := by
    have hid : (d : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2)
        = (a : ℤ) * ((a : ℤ) * d + (b : ℤ) * c) - (b : ℤ) * ((a : ℤ) * c + (b : ℤ) * d) := by ring
    rw [hid]
    exact dvd_sub (hQZ.mul_left _) (hPZ.mul_left _)
  obtain ⟨u, v, huv⟩ : IsCoprime (c : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.2 hcd
  have hdiff : (p : ℤ) ∣ (a : ℤ) ^ 2 - (b : ℤ) ^ 2 := by
    have hid : (a : ℤ) ^ 2 - (b : ℤ) ^ 2
        = u * ((c : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2))
          + v * ((d : ℤ) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2)) := by
      have : (u * (c : ℤ) + v * (d : ℤ)) * ((a : ℤ) ^ 2 - (b : ℤ) ^ 2)
          = (a : ℤ) ^ 2 - (b : ℤ) ^ 2 := by rw [huv]; ring
      linarith [this]
    rw [hid]
    exact dvd_add (hc1.mul_left _) (hd1.mul_left _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hpN
    omega
  have hpnot2 : ¬ (p : ℤ) ∣ 2 := by
    intro hcon
    have hd2 : p ∣ 2 := by exact_mod_cast hcon
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd2)
  have hpa : (p : ℤ) ∣ (a : ℤ) := by
    have h2a : (p : ℤ) ∣ 2 * (a : ℤ) ^ 2 := by
      have : 2 * (a : ℤ) ^ 2 = ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) + ((a : ℤ) ^ 2 - (b : ℤ) ^ 2) := by ring
      rw [this]; exact dvd_add hNZ hdiff
    rcases hpZ.dvd_mul.1 h2a with h | h
    · exact absurd h hpnot2
    · exact hpZ.dvd_of_dvd_pow h
  have hpb : (p : ℤ) ∣ (b : ℤ) := by
    have h2b : (p : ℤ) ∣ 2 * (b : ℤ) ^ 2 := by
      have : 2 * (b : ℤ) ^ 2 = ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) - ((a : ℤ) ^ 2 - (b : ℤ) ^ 2) := by ring
      rw [this]; exact dvd_sub hNZ hdiff
    rcases hpZ.dvd_mul.1 h2b with h | h
    · exact absurd h hpnot2
    · exact hpZ.dvd_of_dvd_pow h
  have hpa' : p ∣ a := by exact_mod_cast hpa
  have hpb' : p ∣ b := by exact_mod_cast hpb
  have : p ∣ 1 := hab ▸ Nat.dvd_gcd hpa' hpb'
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.1 this)

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem euler_gcd_product {a b c d N : ℕ} (hodd : N % 2 = 1)
    (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d)
    (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N) :
    Nat.gcd N (a * c + b * d) * Nat.gcd N (a * d + b * c) = N := by
  set P := a * c + b * d with hP
  set Q := a * d + b * c with hQ
  set S := a * b + c * d with hS
  have hPQ : P * Q = N * S := HyperbolicBerggrenGeodesics.euler_cross_product h1 h2
  have hstep : P * Nat.gcd N Q = N * Nat.gcd P S := by
    rw [← Nat.gcd_mul_left P N Q, mul_comm P N, hPQ, Nat.gcd_mul_left N P S]
  have hcop : Nat.gcd (Nat.gcd N Q) (Nat.gcd P S) = 1 := by
    have hdvd : Nat.gcd (Nat.gcd N Q) (Nat.gcd P S) ∣ Nat.gcd (Nat.gcd N P) Q := by
      refine Nat.dvd_gcd (Nat.dvd_gcd ?_ ?_) ?_
      · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
      · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    exact Nat.eq_one_of_dvd_one (HyperbolicBerggrenGeodesics.collision_gcd_three_eq_one hodd hab hcd h1 ▸ hdvd)
  calc Nat.gcd N P * Nat.gcd N Q
      = Nat.gcd (N * Nat.gcd N Q) (P * Nat.gcd N Q) := (Nat.gcd_mul_right N (Nat.gcd N Q) P).symm
    _ = Nat.gcd (N * Nat.gcd N Q) (N * Nat.gcd P S) := by rw [hstep]
    _ = N * Nat.gcd (Nat.gcd N Q) (Nat.gcd P S) := Nat.gcd_mul_left _ _ _
    _ = N := by rw [hcop, mul_one]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem berggren_collision_splits {m₁ n₁ m₂ n₂ N : ℕ} (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hN₁ : m₁ ^ 2 + n₁ ^ 2 = N) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = N) (hne : (m₁, n₁) ≠ (m₂, n₂)) :
    Nat.gcd N (m₁ * m₂ + n₁ * n₂) * Nat.gcd N (m₁ * n₂ + n₁ * m₂) = N ∧
      1 < Nat.gcd N (m₁ * m₂ + n₁ * n₂) ∧ Nat.gcd N (m₁ * m₂ + n₁ * n₂) < N ∧
      1 < Nat.gcd N (m₁ * n₂ + n₁ * m₂) ∧ Nat.gcd N (m₁ * n₂ + n₁ * m₂) < N := by
  have hodd : N % 2 = 1 := hN₁ ▸ HyperbolicBerggrenGeodesics.seed_hypotenuse_odd h₁
  have hprod := HyperbolicBerggrenGeodesics.euler_gcd_product hodd h₁.cop h₂.cop hN₁ hN₂
  obtain ⟨hlow, hhigh⟩ := berggren_collision_factors h₁ h₂ hN₁ hN₂ hne
  have hNpos : 0 < N := by omega
  refine ⟨hprod, hlow, hhigh, ?_, ?_⟩
  · -- if the second factor were `0` or `1`, the first would be `0` or `N`
    rcases Nat.eq_zero_or_pos (Nat.gcd N (m₁ * n₂ + n₁ * m₂)) with hz | hpos
    · rw [hz, mul_zero] at hprod; omega
    · rcases Nat.lt_or_ge 1 (Nat.gcd N (m₁ * n₂ + n₁ * m₂)) with hlt | hle
      · exact hlt
      · exfalso
        have hone : Nat.gcd N (m₁ * n₂ + n₁ * m₂) = 1 := by omega
        rw [hone, mul_one] at hprod
        omega
  · -- likewise the second factor cannot be all of `N`
    have hle : Nat.gcd N (m₁ * n₂ + n₁ * m₂) ≤ N :=
      Nat.le_of_dvd hNpos (Nat.gcd_dvd_left _ _)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      rw [h] at hprod
      have hone : Nat.gcd N (m₁ * m₂ + n₁ * n₂) = 1 :=
        Nat.eq_of_mul_eq_mul_right hNpos (by rw [hprod, one_mul])
      omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem collFamilyA_isSeed (j : ℕ) : IsSeed (20 * j + 9) (10 * j + 2) := by
  refine ⟨by omega, by omega, ?_, by omega⟩
  have h1 : Nat.gcd (20 * j + 9) (10 * j + 2) ∣ 20 * j + 9 := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (20 * j + 9) (10 * j + 2) ∣ 10 * j + 2 := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (20 * j + 9) (10 * j + 2) ∣ 20 * j + 4 := by
    have := h2.mul_left 2
    simpa [show 2 * (10 * j + 2) = 20 * j + 4 by ring] using this
  have h4 : Nat.gcd (20 * j + 9) (10 * j + 2) ∣ 5 := by
    simpa [show 20 * j + 9 - (20 * j + 4) = 5 by omega] using Nat.dvd_sub h1 h3
  rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h4) with h | h
  · exact h
  · exfalso
    rw [h] at h2
    obtain ⟨t, ht⟩ := h2
    omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem collFamilyB_isSeed (j : ℕ) : IsSeed (20 * j + 7) (10 * j + 6) := by
  refine ⟨by omega, by omega, ?_, by omega⟩
  have h1 : Nat.gcd (20 * j + 7) (10 * j + 6) ∣ 20 * j + 7 := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (20 * j + 7) (10 * j + 6) ∣ 10 * j + 6 := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (20 * j + 7) (10 * j + 6) ∣ 20 * j + 12 := by
    have := h2.mul_left 2
    simpa [show 2 * (10 * j + 6) = 20 * j + 12 by ring] using this
  have h4 : Nat.gcd (20 * j + 7) (10 * j + 6) ∣ 5 := by
    simpa [show 20 * j + 12 - (20 * j + 7) = 5 by omega] using Nat.dvd_sub h3 h1
  rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h4) with h | h
  · exact h
  · exfalso
    rw [h] at h2
    obtain ⟨t, ht⟩ := h2
    omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem collFamily_hyp_A (j : ℕ) :
    (20 * j + 9) ^ 2 + (10 * j + 2) ^ 2 = 500 * j ^ 2 + 400 * j + 85 := by ring

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem collFamily_hyp_B (j : ℕ) :
    (20 * j + 7) ^ 2 + (10 * j + 6) ^ 2 = 500 * j ^ 2 + 400 * j + 85 := by ring

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem exists_collision_gt (M : ℕ) :
    ∃ N m₁ n₁ m₂ n₂ : ℕ, M < N ∧ IsSeed m₁ n₁ ∧ IsSeed m₂ n₂ ∧
      m₁ ^ 2 + n₁ ^ 2 = N ∧ m₂ ^ 2 + n₂ ^ 2 = N ∧ (m₁, n₁) ≠ (m₂, n₂) := by
  refine ⟨500 * M ^ 2 + 400 * M + 85, 20 * M + 9, 10 * M + 2, 20 * M + 7, 10 * M + 6, ?_,
    collFamilyA_isSeed M, HyperbolicBerggrenGeodesics.collFamilyB_isSeed M, HyperbolicBerggrenGeodesics.collFamily_hyp_A M, HyperbolicBerggrenGeodesics.collFamily_hyp_B M, ?_⟩
  · nlinarith [sq_nonneg M]
  · simp only [ne_eq, Prod.mk.injEq, not_and]
    omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem gcd_add_ten_eq_five {P : ℕ} (h5P : 5 ∣ P) (hodd : P % 2 = 1) :
    Nat.gcd (P + 10) P = 5 := by
  have h5N : (5 : ℕ) ∣ P + 10 := Dvd.dvd.add h5P (by norm_num)
  have h5g : (5 : ℕ) ∣ Nat.gcd (P + 10) P := Nat.dvd_gcd h5N h5P
  have hgN : Nat.gcd (P + 10) P ∣ P + 10 := Nat.gcd_dvd_left _ _
  have hgP : Nat.gcd (P + 10) P ∣ P := Nat.gcd_dvd_right _ _
  have hg10 : Nat.gcd (P + 10) P ∣ 10 := by
    simpa using Nat.dvd_sub hgN hgP
  have hle : Nat.gcd (P + 10) P ≤ 10 := Nat.le_of_dvd (by norm_num) hg10
  obtain ⟨t, ht⟩ := h5g
  have htle : t ≤ 2 := by omega
  interval_cases t
  · exfalso
    rw [Nat.mul_zero] at ht
    rw [ht] at hgP
    have hP0 : P = 0 := Nat.eq_zero_of_zero_dvd hgP
    omega
  · omega
  · exfalso
    rw [show 5 * 2 = 10 from rfl] at ht
    rw [ht] at hgN
    obtain ⟨s, hs⟩ := hgN
    omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem collFamily_divisor (j : ℕ) :
    Nat.gcd (500 * j ^ 2 + 400 * j + 85)
      ((20 * j + 9) * (20 * j + 7) + (10 * j + 2) * (10 * j + 6)) = 5 := by
  have hP : (20 * j + 9) * (20 * j + 7) + (10 * j + 2) * (10 * j + 6)
      = 500 * j ^ 2 + 400 * j + 75 := by ring
  have hN : 500 * j ^ 2 + 400 * j + 85 = (500 * j ^ 2 + 400 * j + 75) + 10 := by ring
  rw [hP, hN]
  refine HyperbolicBerggrenGeodesics.gcd_add_ten_eq_five ⟨100 * j ^ 2 + 80 * j + 15, by ring⟩ ?_
  omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem card_multiples_Ioc (k a b : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter (fun x => k ∣ x)).card = b / k - a / k := by
  have hsub : (Finset.Ioc 0 a).filter (fun x => k ∣ x)
      ⊆ (Finset.Ioc 0 b).filter (fun x => k ∣ x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
    exact ⟨⟨hx.1.1, hx.1.2.trans hab⟩, hx.2⟩
  have hEq : (Finset.Ioc a b).filter (fun x => k ∣ x)
      = ((Finset.Ioc 0 b).filter (fun x => k ∣ x)) \ ((Finset.Ioc 0 a).filter (fun x => k ∣ x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, not_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨by omega, h2⟩, h3⟩, by intro hc; omega⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      refine ⟨⟨?_, h2⟩, h3⟩
      by_contra hc
      exact absurd h3 (h4 ⟨h1, by omega⟩)
  rw [hEq, Finset.card_sdiff_of_subset hsub, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem add_div_le_add_div (a b k : ℕ) : (a + b) / k ≤ a / k + b / k + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · omega
  · have hma := Nat.mod_lt a h
    have hmb := Nat.mod_lt b h
    have hsplit : a + b = k * (a / k + b / k) + (a % k + b % k) := by
      have hka := Nat.div_add_mod a k
      have hkb := Nat.div_add_mod b k
      have : k * (a / k + b / k) = k * (a / k) + k * (b / k) := by ring
      omega
    rw [hsplit, Nat.mul_add_div h]
    have : (a % k + b % k) / k < 2 := (Nat.div_lt_iff_lt_mul h).2 (by omega)
    omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem sum_inv_sq_odd (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / (2 * (i : ℝ) + 3) ^ 2 ≤ 1 / 4 - 1 / (4 * (n : ℝ) + 4) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have key : (1 : ℝ) / (2 * (n : ℝ) + 3) ^ 2
        ≤ 1 / (4 * (n : ℝ) + 4) - 1 / (4 * ((n : ℝ) + 1) + 4) := by
      have e : 1 / (4 * (n : ℝ) + 4) - 1 / (4 * ((n : ℝ) + 1) + 4)
          = 4 / ((4 * (n : ℝ) + 4) * (4 * (n : ℝ) + 8)) := by
        field_simp
        ring
      rw [e]
      refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
      nlinarith [sq_nonneg ((n : ℝ))]
    push_cast
    linarith [ih]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem sum_inv_odd (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / (2 * (i : ℝ) + 3) ≤ Real.sqrt (2 * (n : ℝ) + 1) - 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    set u := Real.sqrt (2 * (n : ℝ) + 1) with hu
    have hu2 : u ^ 2 = 2 * (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hupos : 0 < u := Real.sqrt_pos.2 (by positivity)
    have hveq : Real.sqrt (2 * ((n : ℝ) + 1) + 1) = Real.sqrt (2 * (n : ℝ) + 3) := by
      congr 1; ring
    set v := Real.sqrt (2 * (n : ℝ) + 3) with hv
    have hv2 : v ^ 2 = 2 * (n : ℝ) + 3 := Real.sq_sqrt (by positivity)
    have hvpos : 0 < v := Real.sqrt_pos.2 (by positivity)
    have hv1 : 1 ≤ v := by nlinarith
    have key : (1 : ℝ) / (2 * (n : ℝ) + 3) ≤ v - u := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (v - u), sq_nonneg (v + u)]
    push_cast
    rw [hveq]
    linarith [ih]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem card_evenBox (K : ℕ) : (evenBox K).card = K := by
  rw [evenBox, HyperbolicBerggrenGeodesics.card_multiples_Ioc 2 (2 * K) (4 * K) (by omega)]
  omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem card_oddBox (K : ℕ) : (oddBox K).card = K := by
  have hall : (Finset.Icc 1 (2 * K)).card = 2 * K := by simp
  have hhalf : ((Finset.Icc 1 (2 * K)).filter (fun n => 2 ∣ n)).card = K := by
    have hIcc : Finset.Icc 1 (2 * K) = Finset.Ioc 0 (2 * K) := by
      ext x; simp [Nat.lt_iff_add_one_le]
    rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 (2 * K)) (p := fun n => 2 ∣ n)
  rw [oddBox]
  omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem mem_seedBox_isSeed {K : ℕ} {p : ℕ × ℕ} (hp : p ∈ seedBox K) : IsSeed p.1 p.2 := by
  rw [seedBox, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hm, hn⟩, hcop⟩ := hp
  rw [evenBox, Finset.mem_filter, Finset.mem_Ioc] at hm
  rw [oddBox, Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hm1, hm2⟩, hm3⟩ := hm
  obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
  refine ⟨by omega, by omega, hcop, ?_⟩
  omega

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem card_evenBox_filter {K d : ℕ} (hd : ¬ 2 ∣ d) :
    ((evenBox K).filter (fun m => d ∣ m)).card ≤ K / d + 1 := by
  have hcop : Nat.Coprime 2 d := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hd
  have hset : (evenBox K).filter (fun m => d ∣ m)
      = (Finset.Ioc (2 * K) (4 * K)).filter (fun m => 2 * d ∣ m) := by
    rw [evenBox, Finset.filter_filter]
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨h2, hdx⟩
      exact hcop.mul_dvd_of_dvd_of_dvd h2 hdx
    · intro h
      exact ⟨dvd_trans ⟨d, rfl⟩ h, dvd_trans ⟨2, by ring⟩ h⟩
  rw [hset, HyperbolicBerggrenGeodesics.card_multiples_Ioc _ _ _ (by omega)]
  have h1 : 4 * K / (2 * d) = 2 * K / d := by
    rw [show 4 * K = 2 * (2 * K) by ring, Nat.mul_div_mul_left _ _ (by omega)]
  have h2 : 2 * K / (2 * d) = K / d := Nat.mul_div_mul_left _ _ (by omega)
  rw [h1, h2]
  have h3 : 2 * K / d ≤ K / d + K / d + 1 := by
    have h := HyperbolicBerggrenGeodesics.add_div_le_add_div K K d
    rwa [show K + K = 2 * K from (two_mul K).symm] at h
  exact Nat.sub_le_iff_le_add.2 (by linarith)

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem card_oddBox_filter (K d : ℕ) :
    ((oddBox K).filter (fun n => d ∣ n)).card ≤ 2 * K / d := by
  have hsub : (oddBox K).filter (fun n => d ∣ n)
      ⊆ (Finset.Ioc 0 (2 * K)).filter (fun n => d ∣ n) := by
    intro x hx
    rw [oddBox, Finset.filter_filter, Finset.mem_filter, Finset.mem_Icc] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, hx.2.2⟩
  have := Finset.card_le_card hsub
  rwa [Nat.Ioc_filter_dvd_card_eq_div] at this

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem bad_subset {K : ℕ} :
    ((evenBox K ×ˢ oddBox K).filter (fun p => ¬ Nat.Coprime p.1 p.2))
      ⊆ (oddDivs K).biUnion (fun d =>
          ((evenBox K).filter (fun m => d ∣ m)) ×ˢ ((oddBox K).filter (fun n => d ∣ n))) := by
  intro p hp
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hm, hn⟩, hcop⟩ := hp
  have hn' := hn
  rw [oddBox, Finset.mem_filter, Finset.mem_Icc] at hn'
  obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn'
  set d := Nat.gcd p.1 p.2 with hd
  have hdm : d ∣ p.1 := Nat.gcd_dvd_left _ _
  have hdn : d ∣ p.2 := Nat.gcd_dvd_right _ _
  have hdle : d ≤ p.2 := Nat.le_of_dvd (by omega) hdn
  have hdodd : ¬ 2 ∣ d := fun h2 => hn3 (h2.trans hdn)
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hdn
    omega
  have hd1 : d ≠ 1 := hcop
  have hd3 : 3 ≤ d := by
    rcases Nat.lt_or_ge d 3 with h | h
    · interval_cases d
      · exact absurd rfl hd0
      · exact absurd rfl hd1
      · exact absurd ⟨1, rfl⟩ hdodd
    · exact h
  refine Finset.mem_biUnion.2 ⟨d, ?_, ?_⟩
  · rw [oddDivs, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hd3, by omega⟩, hdodd⟩
  · exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hm, hdm⟩, Finset.mem_filter.2 ⟨hn, hdn⟩⟩

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem card_bad_le (K : ℕ) :
    ((evenBox K ×ˢ oddBox K).filter (fun p => ¬ Nat.Coprime p.1 p.2)).card
      ≤ ∑ d ∈ oddDivs K, (K / d + 1) * (2 * K / d) := by
  refine le_trans (Finset.card_le_card HyperbolicBerggrenGeodesics.bad_subset) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  refine Finset.sum_le_sum ?_
  intro d hd
  rw [oddDivs, Finset.mem_filter, Finset.mem_Icc] at hd
  rw [Finset.card_product]
  exact Nat.mul_le_mul (HyperbolicBerggrenGeodesics.card_evenBox_filter hd.2) (HyperbolicBerggrenGeodesics.card_oddBox_filter K d)

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem sum_bad_real_le (K : ℕ) :
    (((∑ d ∈ oddDivs K, (K / d + 1) * (2 * K / d) : ℕ)) : ℝ)
      ≤ (K : ℝ) ^ 2 / 2 + 2 * (K : ℝ) * Real.sqrt (2 * (K : ℝ) + 1) := by
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  rw [Nat.cast_sum]
  set g : ℕ → ℝ := fun d => ((K : ℝ) / (d : ℝ) + 1) * (2 * (K : ℝ) / (d : ℝ)) with hg
  -- each term is bounded by its real counterpart
  have hterm : ∀ d ∈ oddDivs K, (((K / d + 1) * (2 * K / d) : ℕ) : ℝ) ≤ g d := by
    intro d hd
    rw [oddDivs, Finset.mem_filter, Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      have : 0 < d := by omega
      exact_mod_cast this
    push_cast
    have h1 : (((K / d : ℕ)) : ℝ) ≤ (K : ℝ) / d := Nat.cast_div_le
    have h2 : (((2 * K / d : ℕ)) : ℝ) ≤ (2 * (K : ℝ)) / d := by
      have := Nat.cast_div_le (α := ℝ) (m := 2 * K) (n := d)
      push_cast at this
      linarith
    have h3 : (0 : ℝ) ≤ (((2 * K / d : ℕ)) : ℝ) := Nat.cast_nonneg _
    rw [hg]
    nlinarith [Nat.cast_nonneg (α := ℝ) (K / d)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- reindex the odd divisors as `2i+3`
  have hsub : oddDivs K ⊆ (Finset.range K).image (fun i => 2 * i + 3) := by
    intro d hd
    rw [oddDivs, Finset.mem_filter, Finset.mem_Icc] at hd
    refine Finset.mem_image.2 ⟨(d - 3) / 2, Finset.mem_range.2 (by omega), ?_⟩
    omega
  have hnonneg : ∀ d ∈ (Finset.range K).image (fun i => 2 * i + 3),
      d ∉ oddDivs K → (0 : ℝ) ≤ g d := by
    intro d hd _
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    rw [hg]
    positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg) ?_
  have hinj : Set.InjOn (fun i => 2 * i + 3) (Finset.range K) := by
    intro x _ y _ h
    dsimp only at h
    omega
  rw [Finset.sum_image hinj]
  -- split into the `1/d²` and `1/d` parts
  have hsplit : ∀ i ∈ Finset.range K,
      g (2 * i + 3)
        = 2 * (K : ℝ) ^ 2 * (1 / (2 * (i : ℝ) + 3) ^ 2)
          + 2 * (K : ℝ) * (1 / (2 * (i : ℝ) + 3)) := by
    intro i _
    have hi : ((2 * i + 3 : ℕ) : ℝ) = 2 * (i : ℝ) + 3 := by push_cast; ring
    rw [hg]
    simp only [hi]
    have hpos : (0 : ℝ) < 2 * (i : ℝ) + 3 := by positivity
    field_simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := HyperbolicBerggrenGeodesics.sum_inv_sq_odd K
  have h2 := HyperbolicBerggrenGeodesics.sum_inv_odd K
  have hs : 0 ≤ Real.sqrt (2 * (K : ℝ) + 1) := Real.sqrt_nonneg _
  have hb1 : 2 * (K : ℝ) ^ 2 * (∑ i ∈ Finset.range K, (1 : ℝ) / (2 * (i : ℝ) + 3) ^ 2)
      ≤ (K : ℝ) ^ 2 / 2 := by
    have hnn : (0 : ℝ) ≤ 2 * (K : ℝ) ^ 2 := by positivity
    have : (∑ i ∈ Finset.range K, (1 : ℝ) / (2 * (i : ℝ) + 3) ^ 2) ≤ 1 / 4 := by
      have : (0 : ℝ) < 4 * (K : ℝ) + 4 := by positivity
      linarith [h1, one_div_pos.2 this]
    nlinarith
  have hb2 : 2 * (K : ℝ) * (∑ i ∈ Finset.range K, (1 : ℝ) / (2 * (i : ℝ) + 3))
      ≤ 2 * (K : ℝ) * Real.sqrt (2 * (K : ℝ) + 1) := by
    have hnn : (0 : ℝ) ≤ 2 * (K : ℝ) := by positivity
    nlinarith [h2]
  linarith

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem card_seedBox_lower {K : ℕ} (hK : 256 ≤ K) : (K : ℝ) ^ 2 / 4 ≤ ((seedBox K).card : ℝ) := by
  have hKR : (256 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  -- total = good + bad
  have htotal : (evenBox K ×ˢ oddBox K).card = K * K := by
    rw [Finset.card_product, HyperbolicBerggrenGeodesics.card_evenBox, HyperbolicBerggrenGeodesics.card_oddBox]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := evenBox K ×ˢ oddBox K) (p := fun p => Nat.Coprime p.1 p.2)
  have hgood : (seedBox K).card
      + ((evenBox K ×ˢ oddBox K).filter (fun p => ¬ Nat.Coprime p.1 p.2)).card = K * K := by
    rw [seedBox]
    omega
  have hbad : (((evenBox K ×ˢ oddBox K).filter (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ)
      ≤ (K : ℝ) ^ 2 / 2 + 2 * K * Real.sqrt (2 * K + 1) := by
    refine le_trans ?_ (HyperbolicBerggrenGeodesics.sum_bad_real_le K)
    exact_mod_cast HyperbolicBerggrenGeodesics.card_bad_le K
  -- `2 K √(2K+1) ≤ K²/4` for `K ≥ 256`
  have hsq : Real.sqrt (2 * (K : ℝ) + 1) ≤ (K : ℝ) / 8 := by
    rw [show (K : ℝ) / 8 = Real.sqrt (((K : ℝ) / 8) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hfinal : 2 * (K : ℝ) * Real.sqrt (2 * (K : ℝ) + 1) ≤ (K : ℝ) ^ 2 / 4 := by
    nlinarith
  have hcast : ((seedBox K).card : ℝ) + (((evenBox K ×ˢ oddBox K).filter
      (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ) = (K : ℝ) * K := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) hgood
  nlinarith [hbad, hfinal, hcast]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem nodePoint_injOn (K : ℕ) : Set.InjOn nodePoint (seedBox K) := by
  intro p hp q hq hpq
  have hsp := HyperbolicBerggrenGeodesics.mem_seedBox_isSeed (K := K) (by simpa using hp)
  have hsq := HyperbolicBerggrenGeodesics.mem_seedBox_isSeed (K := K) (by simpa using hq)
  have hp0 : 0 < p.1 := lt_trans hsp.pos hsp.lt
  have hq0 : 0 < q.1 := lt_trans hsq.pos hsq.lt
  rw [nodePoint, nodePoint, dif_pos hp0, dif_pos hq0] at hpq
  obtain ⟨h1, h2⟩ := HyperbolicBerggrenGeodesics.hpoint_injective hp0 hq0 hpq
  exact Prod.ext h1 h2

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem nodePoint_dist_le {K : ℕ} (hK : 256 ≤ K) {p : ℕ × ℕ} (hp : p ∈ seedBox K) :
    dist (nodePoint p) UpperHalfPlane.I ≤ Real.log K + 2 := by
  have hs := HyperbolicBerggrenGeodesics.mem_seedBox_isSeed hp
  have hp0 : 0 < p.1 := lt_trans hs.pos hs.lt
  rw [nodePoint, dif_pos hp0]
  have hb := HyperbolicBerggrenGeodesics.dist_le_half_log_two_hypotenuse hs.pos hs.lt
  refine le_trans hb ?_
  -- the box forces `m ≤ 4K` and `n ≤ 2K`, so `2 (c+1) ≤ 42 K² ≤ K² e⁴`
  rw [seedBox, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hm, hn⟩, -⟩ := hp
  rw [evenBox, Finset.mem_filter, Finset.mem_Ioc] at hm
  rw [oddBox, Finset.mem_filter, Finset.mem_Icc] at hn
  have hmle : (p.1 : ℝ) ≤ 4 * K := by exact_mod_cast hm.1.2
  have hnle : (p.2 : ℝ) ≤ 2 * K := by exact_mod_cast hn.1.2
  have hm0 : (0 : ℝ) ≤ (p.1 : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (p.2 : ℝ) := Nat.cast_nonneg _
  have hKR : (256 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hc : 2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 + 1) ≤ 42 * (K : ℝ) ^ 2 := by nlinarith
  have hexp : (42 : ℝ) ≤ Real.exp 4 := by
    have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
    have h2 : Real.exp 4 = (Real.exp 1) ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2.7182818283 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) h1 4
    rw [h2]
    nlinarith [h3]
  have hle : 2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 + 1) ≤ Real.exp 4 * (K : ℝ) ^ 2 := by
    nlinarith
  have hpos : (0 : ℝ) < 2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 + 1) := by positivity
  have hlog : Real.log (2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 + 1))
      ≤ 4 + 2 * Real.log K := by
    have hR : Real.log (Real.exp 4 * (K : ℝ) ^ 2) = 4 + 2 * Real.log K := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow]
      push_cast; ring
    have h1 := Real.log_le_log hpos hle
    rwa [hR] at h1
  linarith

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem hyperbolic_ball_quadratic_growth {K : ℕ} (hK : 256 ≤ K) :
    ∃ (R : ℝ) (S : Finset ℍ), R = Real.log K + 2 ∧
      Real.exp (2 * R) / 300 ≤ (S.card : ℝ) ∧
      ∀ z ∈ S, dist z UpperHalfPlane.I ≤ R := by
  classical
  refine ⟨Real.log K + 2, (seedBox K).image nodePoint, rfl, ?_, ?_⟩
  · have hcard : (((seedBox K).image nodePoint).card : ℝ) = ((seedBox K).card : ℝ) := by
      rw [Finset.card_image_of_injOn (HyperbolicBerggrenGeodesics.nodePoint_injOn K)]
    rw [hcard]
    refine le_trans ?_ (HyperbolicBerggrenGeodesics.card_seedBox_lower hK)
    have hKR : (256 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
    have hexp : Real.exp (2 * (Real.log K + 2)) = Real.exp 4 * (K : ℝ) ^ 2 := by
      rw [show 2 * (Real.log K + 2) = 4 + 2 * Real.log K by ring, Real.exp_add,
        show (2 : ℝ) * Real.log K = Real.log ((K : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity)]
    rw [hexp]
    have h4 : Real.exp 4 ≤ 75 := by
      have h1 : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
      have h2 : Real.exp 4 = (Real.exp 1) ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      have h3 : (Real.exp 1) ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1 4
      rw [h2]
      nlinarith [h3]
    nlinarith [sq_nonneg ((K : ℝ))]
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hz
    exact HyperbolicBerggrenGeodesics.nodePoint_dist_le hK hp

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem ball_card_upper {R : ℝ} (hR : 0 ≤ R) (S : Finset (ℕ × ℕ))
    (hseed : ∀ p ∈ S, IsSeed p.1 p.2)
    (hball : ∀ p ∈ S, ∀ h : 0 < p.1, dist (hpoint p.1 p.2 h) UpperHalfPlane.I ≤ R) :
    (S.card : ℝ) ≤ 4 * Real.exp (2 * R) := by
  classical
  set M : ℕ := ⌊Real.exp R⌋₊ with hM
  have hMle : (M : ℝ) ≤ Real.exp R := Nat.floor_le (Real.exp_pos R).le
  -- every node in the ball has both coordinates at most `M`
  have hsub : S ⊆ Finset.range (M + 1) ×ˢ Finset.range (M + 1) := by
    intro p hp
    have hs := hseed p hp
    have hp0 : 0 < p.1 := lt_trans hs.pos hs.lt
    have hd := hball p hp hp0
    have hlow := HyperbolicBerggrenGeodesics.dist_ge_half_log_hypotenuse hs.pos hs.lt
    have hc0 : (0 : ℝ) < (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
      have : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp0
      positivity
    have hlog : Real.log ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ 2 * R := by linarith
    have hcle : (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ Real.exp (2 * R) := by
      have := Real.exp_le_exp.2 hlog
      rwa [Real.exp_log hc0] at this
    have hm2 : (p.1 : ℝ) ^ 2 ≤ (Real.exp R) ^ 2 := by
      have hn0 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 2 := by positivity
      have hsq : (Real.exp R) ^ 2 = Real.exp (2 * R) := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [hsq]
      linarith
    have hmle : (p.1 : ℝ) ≤ Real.exp R := by
      nlinarith [Nat.cast_nonneg (α := ℝ) p.1, (Real.exp_pos R).le]
    have hmM : p.1 ≤ M := Nat.le_floor hmle
    have hnM : p.2 ≤ M := le_trans hs.lt.le hmM
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  have hcard : S.card ≤ (M + 1) * (M + 1) := by
    simpa [Finset.card_product] using Finset.card_le_card hsub
  have hcardR : (S.card : ℝ) ≤ ((M : ℝ) + 1) * ((M : ℝ) + 1) := by
    have : ((S.card : ℕ) : ℝ) ≤ (((M + 1) * (M + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at this
    linarith
  have he1 : (1 : ℝ) ≤ Real.exp R := Real.one_le_exp hR
  have hsq : (Real.exp R) ^ 2 = Real.exp (2 * R) := by
    rw [← Real.exp_nat_mul]; ring_nf
  nlinarith [Nat.cast_nonneg (α := ℝ) M]

end HyperbolicBerggrenGeodesics

namespace HyperbolicBerggrenGeodesics

theorem semiprime_collision_splits_exactly {m₁ n₁ m₂ n₂ p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h₁ : IsSeed m₁ n₁) (h₂ : IsSeed m₂ n₂)
    (hN₁ : m₁ ^ 2 + n₁ ^ 2 = p * q) (hN₂ : m₂ ^ 2 + n₂ ^ 2 = p * q)
    (hne : (m₁, n₁) ≠ (m₂, n₂)) :
    (Nat.gcd (p * q) (m₁ * m₂ + n₁ * n₂) = p ∧ Nat.gcd (p * q) (m₁ * n₂ + n₁ * m₂) = q) ∨
      (Nat.gcd (p * q) (m₁ * m₂ + n₁ * n₂) = q ∧ Nat.gcd (p * q) (m₁ * n₂ + n₁ * m₂) = p) := by
  obtain ⟨hprod, hg1, hg2, hh1, hh2⟩ := HyperbolicBerggrenGeodesics.berggren_collision_splits h₁ h₂ hN₁ hN₂ hne
  set g := Nat.gcd (p * q) (m₁ * m₂ + n₁ * n₂) with hgdef
  set h := Nat.gcd (p * q) (m₁ * n₂ + n₁ * m₂) with hhdef
  -- `g` is a divisor of `p q` other than `1` and `p q`, hence `p` or `q`
  have hgdvd : g ∣ p * q := Nat.gcd_dvd_left _ _
  have hgp : g = p ∨ g = q := by
    by_cases hdvd : p ∣ g
    · obtain ⟨t, ht⟩ := hdvd
      have htq : t ∣ q := by
        have : p * t ∣ p * q := ht ▸ hgdvd
        exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.pos.ne' : (p : ℕ) ≠ 0)).1 this
      rcases (hq.eq_one_or_self_of_dvd t htq) with h1 | h1
      · left; rw [ht, h1, mul_one]
      · exfalso; rw [ht, h1] at hg2; omega
    · right
      have hcopg : Nat.Coprime g p := (Nat.Prime.coprime_iff_not_dvd hp).2 hdvd |>.symm
      have : g ∣ q := hcopg.dvd_of_dvd_mul_left hgdvd
      rcases (hq.eq_one_or_self_of_dvd g this) with h1 | h1
      · exact absurd h1 (by omega)
      · exact h1
  have hqpos : 0 < q := hq.pos
  have hppos : 0 < p := hp.pos
  rcases hgp with hgval | hgval
  · left
    refine ⟨hgval, ?_⟩
    rw [hgval] at hprod
    exact Nat.eq_of_mul_eq_mul_left hppos hprod
  · right
    refine ⟨hgval, ?_⟩
    rw [hgval, mul_comm p q] at hprod
    exact Nat.eq_of_mul_eq_mul_left hqpos hprod

end HyperbolicBerggrenGeodesics


theorem solution {K : ℕ} (hK : 256 ≤ K) :
    ∃ (R : ℝ) (S : Finset ℍ), R = Real.log K + 2 ∧
      Real.exp (2 * R) / 300 ≤ (S.card : ℝ) ∧
      ∀ z ∈ S, dist z UpperHalfPlane.I ≤ R := by
  classical
  refine ⟨Real.log K + 2, (seedBox K).image nodePoint, rfl, ?_, ?_⟩
  · have hcard : (((seedBox K).image nodePoint).card : ℝ) = ((seedBox K).card : ℝ) := by
      rw [Finset.card_image_of_injOn (HyperbolicBerggrenGeodesics.nodePoint_injOn K)]
    rw [hcard]
    refine le_trans ?_ (HyperbolicBerggrenGeodesics.card_seedBox_lower hK)
    have hKR : (256 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
    have hexp : Real.exp (2 * (Real.log K + 2)) = Real.exp 4 * (K : ℝ) ^ 2 := by
      rw [show 2 * (Real.log K + 2) = 4 + 2 * Real.log K by ring, Real.exp_add,
        show (2 : ℝ) * Real.log K = Real.log ((K : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity)]
    rw [hexp]
    have h4 : Real.exp 4 ≤ 75 := by
      have h1 : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
      have h2 : Real.exp 4 = (Real.exp 1) ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      have h3 : (Real.exp 1) ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1 4
      rw [h2]
      nlinarith [h3]
    nlinarith [sq_nonneg ((K : ℝ))]
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hz
    exact HyperbolicBerggrenGeodesics.nodePoint_dist_le hK hp

#print axioms solution
