-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.hyperbolic_ball_volume_growth
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:38.940768+00:00
-- url     : https://prove2.me/submissions/9c05c953-71d3-492a-8ca8-4998d0a1a220

-- Thm stub generated from Geometry/HyperbolicBerggrenGeodesics.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics

/-!
# Hyperbolic–Pythagorean Geodesics: the Berggren tree in the Poincaré half-plane

This file develops a rigorous bridge between three a-priori unrelated objects:

* the **Berggren ternary tree** of primitive Pythagorean triples (combinatorics /
  arithmetic),
* the **hyperbolic plane** in the Poincaré upper half-plane model `ℍ`
  (Riemannian geometry), and
* **integer factorization** via Euler's two-representation method (number theory).

## Main results

* `bStepL_triple`, `bStepM_triple`, `bStepR_triple` : the three Berggren matrices
  `B₁, B₂, B₃` acting on Pythagorean triples are conjugate, through the Euclid
  parametrisation `(m,n) ↦ (m²-n², 2mn, m²+n²)`, to the three linear maps
  `(m,n) ↦ (2m-n, m), (2m+n, m), (m+2n, n)` on Euclid seeds.
* `seed_step*_isSeed` : the three seed maps preserve the "primitive seed" conditions
  (`0 < n < m`, `gcd m n = 1`, opposite parity).
* `cosh_dist_hpoint_I` : the exact hyperbolic cosine of the distance from the base
  point `i` to the node point `z(m,n) = (n + i)/m`, namely `(m² + n² + 1)/(2m)`.
* `hyperbolic_dist_eq_half_log_hypotenuse` : **the logarithmic trajectory theorem.**
  For every Euclid seed with hypotenuse `c = m² + n²`,
  `|d_ℍ(i, z(m,n)) - ½ log c| ≤ log 2`.
  So *every* node of the Berggren tree, no matter how deep, sits at hyperbolic
  distance `½ log c + O(1)` from the root: the geodesic trajectory is
  logarithmic — sub-linear — in the size of the triple.
* `combDepth_hypotenuse` and `no_logarithmic_depth_bound` : by contrast the
  *combinatorial* depth is **not** logarithmic. The spine `(2,1) → (3,2) → (4,3) → …`
  has depth `k` and hypotenuse only `2k² + 6k + 5`, so depth is `Θ(√c)` there.
  Hence the hyperbolic metric compresses the tree exponentially.
* `hyperbolic_ball_volume_growth` : a **no-free-lunch** theorem. The number of
  Berggren nodes inside the hyperbolic ball of radius `R` around `i` grows like
  `e^{R}`, i.e. like the hypotenuse itself. A short geodesic does not make the
  search cheap.
* `geodesic_energy_lower_bound` : the Cauchy–Schwarz bound `E ≥ d²/k` relating the
  discrete energy of a `k`-step trajectory to the hyperbolic displacement, and
  `berggren_path_energy_lower_bound`, its specialisation to Berggren paths.
* `euler_two_representations_factor` : two essentially distinct representations
  `N = a² + b² = c² + d²` produce a **non-trivial divisor** `gcd(N, ac+bd)` of `N`.
* `berggren_collision_factors` : two distinct Berggren nodes sharing a hypotenuse
  `N` factor `N`.

## Design notes

Distances are Mathlib's genuine hyperbolic metric on `UpperHalfPlane` (`ℍ`), not a
hand-rolled surrogate; `UpperHalfPlane.cosh_dist'` is the only geometric input.
-/

open HyperbolicBerggrenGeodesics

open Real

noncomputable section

/-! ## Part 1. Euclid seeds and the Berggren tree in seed coordinates -/


















/-! ## Part 2. The hyperbolic embedding and the logarithmic trajectory theorem -/

open UpperHalfPlane








/-! ## Part 3. The spine: combinatorial depth is *not* logarithmic -/

open Real
open UpperHalfPlane
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


theorem solution (K : ℕ) :
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

#print axioms solution
