-- Prove2me | solution 1 for LinearOptimization.polyhedron_full_dim_volume_lower_bound_nonstrict
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T04:11:46.093539+00:00
-- url     : https://prove2.me/submissions/572766cc-ec95-418f-850a-be102e34342f

import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_polyhedron_bounded_convex_hull_extreme
import Definitions.Def_LinearOptimization_Ellipsoid
import Mathlib.Analysis.Convex.Measure
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open Matrix MeasureTheory Set
open LinearOptimization

private theorem extreme_point_common_denominator {m n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (U : ℤ)
    (hA : ∀ i j, |A i j| ≤ U) (hb : ∀ i, |b i| ≤ U)
    (x : Fin n → ℝ)
    (hx : x ∈ Set.extremePoints ℝ
      (polyhedron (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ)))) :
    ∃ q : ℤ, ∃ p : Fin n → ℤ,
      q ≠ 0 ∧ 0 ≤ U ∧
      ((|q| : ℤ) : ℝ) ≤ ((n : ℝ) * (U : ℝ)) ^ n ∧
      ∀ j, x j = (p j : ℝ) / (q : ℝ) := by
  classical
  let Ar : Matrix (Fin m) (Fin n) ℝ := A.map ((↑) : ℤ → ℝ)
  let br : Fin m → ℝ := fun i => (b i : ℝ)
  let C := generalFormSystem Ar br
  have hxP : x ∈ polyhedron Ar br := extremePoints_subset hx
  have hxC : x ∈ constraintSet C := by simpa [C]
  have hxextC : x ∈ Set.extremePoints ℝ (constraintSet C) := by
    simpa [C, Ar, br] using hx
  have ht := lp_vertex_extreme_bfs_equiv C x ⟨x, hxC⟩ hxC
  have hbfs : IsBasicFeasibleSolution C x := (ht.out 1 2).mp hxextC
  rcases hbfs.1.2 with ⟨s, hs_card, hs_active, hs_li⟩
  let e : Fin n ≃ s := Fintype.equivOfCardEq (by simp [hs_card])
  let Bz : Matrix (Fin n) (Fin n) ℤ := fun i k => A (e i) k
  let cz : Fin n → ℤ := fun i => b (e i)
  let B : Matrix (Fin n) (Fin n) ℝ := Bz.map ((↑) : ℤ → ℝ)
  let c : Fin n → ℝ := fun i => (cz i : ℝ)
  have hB_li : LinearIndependent ℝ (fun i => B i) := by
    have hcomp := hs_li.comp e e.injective
    simpa [B, Bz, C, generalFormSystem, Ar] using hcomp
  have hBunitM : IsUnit B := Matrix.linearIndependent_rows_iff_isUnit.mp hB_li
  have hBunit : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBunitM
  have hBx : B.mulVec x = c := by
    ext i
    have hi := hs_active (e i) (e i).property
    simpa [LinearConstraint.IsActiveAt, C, generalFormSystem, Ar, B, Bz, c, cz,
      dotProduct, mulVec] using hi
  have hBzdet0 : Bz.det ≠ 0 := by
    intro hzero
    apply hBunit.ne_zero
    rw [show B.det = (Bz.det : ℝ) by
      change ((Int.castRingHom ℝ).mapMatrix Bz).det = (Bz.det : ℝ)
      rw [← RingHom.map_det]
      rfl, hzero]
    simp
  let q : ℤ := Bz.det
  let p : Fin n → ℤ := fun j => (Bz.updateCol j cz).det
  have hcastB : B.det = (q : ℝ) := by
    change B.det = (Bz.det : ℝ)
    change ((Int.castRingHom ℝ).mapMatrix Bz).det = (Bz.det : ℝ)
    rw [← RingHom.map_det]
    rfl
  have hcastUpdate (j : Fin n) : (B.updateCol j c).det = (p j : ℝ) := by
    change (B.updateCol j c).det = ((Bz.updateCol j cz).det : ℝ)
    have heq : B.updateCol j c =
        (Bz.updateCol j cz).map ((↑) : ℤ → ℝ) := by
      ext i k
      by_cases hkj : k = j
      · subst k
        simp [B, c, cz]
      · simp [B, c, cz, hkj]
    rw [heq]
    change ((Int.castRingHom ℝ).mapMatrix (Bz.updateCol j cz)).det = _
    rw [← RingHom.map_det]
    rfl
  have hrepr (j : Fin n) : x j = (p j : ℝ) / (q : ℝ) := by
    have hcramer := congrFun (B.det_smul_inv_mulVec_eq_cramer c hBunit) j
    have hxinv : x = B⁻¹.mulVec c := by
      have h := congrArg (B⁻¹.mulVec) hBx
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hBunit] at h
      simpa using h
    rw [← hxinv, Matrix.cramer_apply, hcastB, hcastUpdate] at hcramer
    apply (eq_div_iff (Int.cast_ne_zero.mpr hBzdet0)).2
    simpa [mul_comm] using hcramer
  have hU0 : 0 ≤ U := by
    let i0 : Fin n := ⟨0, hn⟩
    exact (abs_nonneg (A (e i0) i0)).trans (hA (e i0) i0)
  have hBentry : ∀ i j, |B i j| ≤ (U : ℝ) := by
    intro i j
    simp only [B, Bz, Matrix.map_apply, Int.cast_abs]
    exact_mod_cast hA (e i) j
  have hBdet : |B.det| ≤ (n.factorial : ℝ) * (U : ℝ) ^ n := by
    simpa [nsmul_eq_mul] using
      (Matrix.det_le (A := B) (abv := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ)) hBentry)
  have hfac : (n.factorial : ℝ) * (U : ℝ) ^ n ≤
      ((n : ℝ) * (U : ℝ)) ^ n := by
    rw [mul_pow]
    gcongr
    exact_mod_cast n.factorial_le_pow
  refine ⟨q, p, ?_, hU0, ?_, hrepr⟩
  · exact hBzdet0
  · calc
      ((|q| : ℤ) : ℝ) = |(q : ℝ)| := by exact_mod_cast rfl
      _ = |B.det| := by rw [hcastB]
      _ ≤ ((n : ℝ) * (U : ℝ)) ^ n := hBdet.trans hfac

theorem solution {m n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (U : ℤ)
    (hA : ∀ i j, |A i j| ≤ U) (hb : ∀ i, |b i| ≤ U)
    (hbdd : LinearOptimization.IsBoundedSet
      (LinearOptimization.polyhedron
        (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))))
    (hfull : LinearOptimization.IsFullDimensional
      (LinearOptimization.polyhedron
        (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ)))) :
    ENNReal.ofReal
        (((n : ℝ) ^ n * ((n : ℝ) * (U : ℝ)) ^ (n ^ 2 * (n + 1)))⁻¹) ≤
      volume (LinearOptimization.polyhedron
        (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))) := by
  classical
  let Ar : Matrix (Fin m) (Fin n) ℝ := A.map ((↑) : ℤ → ℝ)
  let br : Fin m → ℝ := fun i => (b i : ℝ)
  let P : Set (Fin n → ℝ) := polyhedron Ar br
  have hPpos : 0 < volume P := by simpa [P, Ar, br, IsFullDimensional] using hfull
  have hPne : P.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, measure_empty] at hPpos
    exact (lt_irrefl 0 hPpos)
  let E : Set (Fin n → ℝ) := Set.extremePoints ℝ P
  have hconv : P = convexHull ℝ E := by
    simpa [P, E, Ar, br] using
      (polyhedron_bounded_convex_hull_extreme Ar br hPne hbdd)
  have hspan : affineSpan ℝ E = ⊤ := by
    by_contra hne
    have hsub : P ⊆ (affineSpan ℝ E : Set (Fin n → ℝ)) := by
      rw [hconv]
      exact convexHull_subset_affineSpan E
    have hzero : volume (affineSpan ℝ E : Set (Fin n → ℝ)) = 0 :=
      Measure.addHaar_affineSubspace volume (affineSpan ℝ E) hne
    have hmono : volume P ≤ volume (affineSpan ℝ E : Set (Fin n → ℝ)) :=
      measure_mono hsub
    rw [hzero] at hmono
    exact (not_lt_of_ge hmono) hPpos
  obtain ⟨s, hsE, bas, hbas⟩ := AffineBasis.exists_affine_subbasis hspan
  letI : Finite s := bas.finite
  letI : Fintype s := Fintype.ofFinite s
  have hcard : Fintype.card s = n + 1 := by
    rw [bas.card_eq_finrank_add_one]
    simp
  let e : s ≃ Fin (n + 1) := Fintype.equivOfCardEq (by simpa using hcard)
  let bas' : AffineBasis (Fin (n + 1)) ℝ (Fin n → ℝ) := bas.reindex e
  let v : Fin (n + 1) → (Fin n → ℝ) := bas'
  have hvaff : AffineIndependent ℝ v := bas'.ind
  have hvE (k : Fin (n + 1)) : v k ∈ E := by
    apply hsE
    change (bas (e.symm k) : Fin n → ℝ) ∈ s
    simpa [hbas]
  have hvext (k : Fin (n + 1)) : v k ∈ Set.extremePoints ℝ P := hvE k
  have hden (k : Fin (n + 1)) :=
    extreme_point_common_denominator hn A b U hA hb (v k) (by
      simpa [P, Ar, br] using hvext k)
  choose q p hq0 hU0 hqB hrepr using hden
  let D : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => v (Fin.succ j) i - v 0 i
  let f : Fin n ↪ {k : Fin (n + 1) // k ≠ 0} :=
    ⟨fun j => ⟨Fin.succ j, Fin.succ_ne_zero j⟩,
      fun i j hij => Fin.succ_injective n (congrArg Subtype.val hij)⟩
  have hvlin : LinearIndependent ℝ
      (fun k : {k : Fin (n + 1) // k ≠ 0} => v k.1 - v 0) := by
    simpa [vsub_eq_sub] using
      ((affineIndependent_iff_linearIndependent_vsub ℝ v 0).mp hvaff)
  have hDcols : LinearIndependent ℝ D.col := by
    have hcomp := hvlin.comp f f.injective
    simpa [D, f, Matrix.col] using hcomp
  have hDunit : IsUnit D := Matrix.linearIndependent_cols_iff_isUnit.mp hDcols
  have hdetD : D.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det D).mp hDunit).ne_zero
  let den : Fin n → ℤ := fun j => q 0 * q (Fin.succ j)
  let Rz : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    p (Fin.succ j) i * q 0 - p 0 i * q (Fin.succ j)
  let R : Matrix (Fin n) (Fin n) ℝ := Rz.map ((↑) : ℤ → ℝ)
  have hDfactor : D = R * Matrix.diagonal (fun j => ((den j : ℤ) : ℝ)⁻¹) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have hq0r : (q 0 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (hq0 0)
    have hqjr : (q (Fin.succ j) : ℝ) ≠ 0 :=
      Int.cast_ne_zero.mpr (hq0 (Fin.succ j))
    simp only [D, R, Rz, Matrix.map_apply, den]
    rw [hrepr (Fin.succ j) i, hrepr 0 i]
    push_cast
    field_simp
  have hcastRdet : R.det = (Rz.det : ℝ) := by
    change ((Int.castRingHom ℝ).mapMatrix Rz).det = (Rz.det : ℝ)
    rw [← RingHom.map_det]
    rfl
  have hdetrel : D.det = (Rz.det : ℝ) * ∏ j, ((den j : ℤ) : ℝ)⁻¹ := by
    rw [hDfactor, Matrix.det_mul, Matrix.det_diagonal, hcastRdet]
  have hRzdet0 : Rz.det ≠ 0 := by
    intro hz
    apply hdetD
    rw [hdetrel, hz]
    simp
  let T : ℝ := ((n : ℝ) * (U : ℝ)) ^ n
  have hT1 : 1 ≤ T := by
    calc
      (1 : ℝ) ≤ ((|q 0| : ℤ) : ℝ) := by
        exact_mod_cast Int.one_le_abs (hq0 0)
      _ ≤ T := by simpa [T] using hqB 0
  have hdenpos (j : Fin n) : 0 < |((den j : ℤ) : ℝ)| := by
    apply abs_pos.mpr
    exact Int.cast_ne_zero.mpr (mul_ne_zero (hq0 0) (hq0 (Fin.succ j)))
  have hdenbound (j : Fin n) : |((den j : ℤ) : ℝ)| ≤ T ^ 2 := by
    calc
      |((den j : ℤ) : ℝ)| =
          ((|q 0| : ℤ) : ℝ) * ((|q (Fin.succ j)| : ℤ) : ℝ) := by
        simp [den, abs_mul]
      _ ≤ T * T := mul_le_mul (by simpa [T] using hqB 0)
          (by simpa [T] using hqB (Fin.succ j)) (by positivity)
          (by positivity)
      _ = T ^ 2 := by ring
  have hprodpos : 0 < ∏ j : Fin n, |((den j : ℤ) : ℝ)| :=
    Finset.prod_pos fun j _ => hdenpos j
  have hprodle : (∏ j : Fin n, |((den j : ℤ) : ℝ)|) ≤ (T ^ 2) ^ n := by
    calc
      (∏ j : Fin n, |((den j : ℤ) : ℝ)|) ≤ ∏ _j : Fin n, T ^ 2 :=
        Finset.prod_le_prod (fun j _ => (hdenpos j).le) (fun j _ => hdenbound j)
      _ = (T ^ 2) ^ n := by simp
  have hupperpos : 0 < (T ^ 2) ^ n := by positivity
  have hinvprod : ((T ^ 2) ^ n)⁻¹ ≤
      (∏ j : Fin n, |((den j : ℤ) : ℝ)|)⁻¹ :=
    (inv_le_inv₀ hupperpos hprodpos).2 hprodle
  have hnum1 : (1 : ℝ) ≤ |(Rz.det : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hRzdet0
  have hdetabs : |D.det| = |(Rz.det : ℝ)| *
      (∏ j : Fin n, |((den j : ℤ) : ℝ)|)⁻¹ := by
    rw [hdetrel, abs_mul, Finset.abs_prod]
    simp_rw [abs_inv]
    rw [Finset.prod_inv_distrib]
  have hdetlower : ((T ^ 2) ^ n)⁻¹ ≤ |D.det| := by
    rw [hdetabs]
    calc
      ((T ^ 2) ^ n)⁻¹ ≤
          (∏ j : Fin n, |((den j : ℤ) : ℝ)|)⁻¹ := hinvprod
      _ = 1 * (∏ j : Fin n, |((den j : ℤ) : ℝ)|)⁻¹ := by ring
      _ ≤ |(Rz.det : ℝ)| * (∏ j : Fin n, |((den j : ℤ) : ℝ)|)⁻¹ :=
        mul_le_mul_of_nonneg_right hnum1 (inv_nonneg.mpr hprodpos.le)
  let r : ℝ := (n : ℝ)⁻¹
  let Cbox : Set (Fin n → ℝ) := Set.Icc 0 (fun _ => r)
  let Sbox : Set (Fin n → ℝ) := (fun t => D.mulVec t) '' Cbox
  let Qbox : Set (Fin n → ℝ) := (fun y => v 0 + y) '' Sbox
  have hrpos : 0 < r := inv_pos.mpr (by exact_mod_cast hn)
  have hPconv : Convex ℝ P := by
    rw [hconv]
    exact convex_convexHull ℝ E
  have hQsub : Qbox ⊆ P := by
    rintro x ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    have ht0 (j : Fin n) : 0 ≤ t j := ht.1 j
    have htr (j : Fin n) : t j ≤ r := ht.2 j
    have hsumle : ∑ j : Fin n, t j ≤ 1 := by
      calc
        ∑ j : Fin n, t j ≤ ∑ _j : Fin n, r :=
          Finset.sum_le_sum fun j _ => htr j
        _ = (n : ℝ) * r := by simp
        _ = 1 := by
          simp [r, Nat.ne_of_gt hn]
    let w : Fin (n + 1) → ℝ :=
      Fin.cases (1 - ∑ j : Fin n, t j) (fun j => t j)
    have hw0 (k : Fin (n + 1)) : 0 ≤ w k := by
      refine Fin.cases ?_ (fun j => ht0 j) k
      dsimp [w]
      linarith
    have hwsum : ∑ k : Fin (n + 1), w k = 1 := by
      rw [Fin.sum_univ_succ]
      simp [w]
    have hcomb : (∑ k : Fin (n + 1), w k • v k) ∈ P := by
      apply hPconv.sum_mem
      · intro k hk
        exact hw0 k
      · exact hwsum
      · intro k hk
        exact extremePoints_subset (hvext k)
    have heq : v 0 + D.mulVec t = ∑ k : Fin (n + 1), w k • v k := by
      ext i
      rw [Fin.sum_univ_succ]
      simp [D, Matrix.mulVec, dotProduct, w]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      have hconst : (∑ x : Fin n, v 0 i * t x) =
          v 0 i * ∑ x : Fin n, t x := by
        rw [Finset.mul_sum]
      have hcomm : (∑ x : Fin n, v (Fin.succ x) i * t x) =
          ∑ x : Fin n, t x * v (Fin.succ x) i := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hconst, hcomm]
      ring
    change v 0 + D.mulVec t ∈ P
    rw [heq]
    exact hcomb
  have hCmeas : MeasurableSet Cbox := by
    exact measurableSet_Icc
  have hCeq : Cbox = Set.pi Set.univ (fun _ : Fin n => Set.Icc 0 r) := by
    ext t
    constructor
    · intro ht i hi
      exact ⟨ht.1 i, ht.2 i⟩
    · intro ht
      constructor
      · intro i
        exact (ht i (Set.mem_univ i)).1
      · intro i
        exact (ht i (Set.mem_univ i)).2
  have hvolC : volume Cbox = ENNReal.ofReal (r ^ n) := by
    rw [hCeq, volume_pi_pi]
    simp [Real.volume_Icc, hrpos.le]
  have hdetUnit : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDunit
  have hdetInv : (D⁻¹).det ≠ 0 :=
    (D.isUnit_nonsing_inv_det hdetUnit).ne_zero
  have hpre : (Matrix.toLin' D⁻¹) ⁻¹' Cbox = Sbox := by
    ext y
    constructor
    · intro hy
      refine ⟨D⁻¹.mulVec y, hy, ?_⟩
      change D.mulVec (D⁻¹.mulVec y) = y
      rw [Matrix.mulVec_mulVec, D.mul_nonsing_inv hdetUnit]
      simp
    · rintro ⟨t, ht, rfl⟩
      change D⁻¹.mulVec (D.mulVec t) ∈ Cbox
      rw [Matrix.mulVec_mulVec, D.nonsing_inv_mul hdetUnit]
      simpa using ht
  have hvolS : volume Sbox = ENNReal.ofReal |D.det| * volume Cbox := by
    have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi
      (M := D⁻¹) hdetInv
    have happ := congrArg (fun μ : Measure (Fin n → ℝ) => μ Cbox) hmap
    change (Measure.map (Matrix.toLin' D⁻¹) volume) Cbox =
      (ENNReal.ofReal |(D⁻¹).det⁻¹| • volume) Cbox at happ
    rw [Measure.map_apply
      (Matrix.toLin' D⁻¹).continuous_of_finiteDimensional.measurable hCmeas, hpre] at happ
    simpa [Measure.smul_apply, Matrix.det_nonsing_inv, abs_inv] using happ
  have hvolQ : volume Qbox = volume Sbox := by
    change volume ((fun y => v 0 + y) '' Sbox) = volume Sbox
    rw [Set.image_add_left, measure_preimage_add]
  let B0 : ℝ := (n : ℝ) * (U : ℝ)
  have hB00 : 0 ≤ B0 := mul_nonneg (by positivity) (by exact_mod_cast hU0 0)
  have hB01 : 1 ≤ B0 := by
    apply (one_le_pow_iff_of_nonneg hB00 (Nat.ne_of_gt hn)).mp
    simpa [T, B0] using hT1
  have hexp : 2 * n ^ 2 ≤ n ^ 2 * (n + 1) := by
    nlinarith
  have hcurrent : (T ^ 2) ^ n = B0 ^ (2 * n ^ 2) := by
    simp only [T, B0]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hpowle : (T ^ 2) ^ n ≤ B0 ^ (n ^ 2 * (n + 1)) := by
    rw [hcurrent]
    exact pow_le_pow_right₀ hB01 hexp
  have hpowpos : 0 < B0 ^ (n ^ 2 * (n + 1)) := by positivity
  have hinvpow : (B0 ^ (n ^ 2 * (n + 1)))⁻¹ ≤ ((T ^ 2) ^ n)⁻¹ :=
    (inv_le_inv₀ hpowpos hupperpos).2 hpowle
  have hreal :
      (((n : ℝ) ^ n * B0 ^ (n ^ 2 * (n + 1)))⁻¹) ≤
        |D.det| * r ^ n := by
    have hnR0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    calc
      (((n : ℝ) ^ n * B0 ^ (n ^ 2 * (n + 1)))⁻¹) =
          r ^ n * (B0 ^ (n ^ 2 * (n + 1)))⁻¹ := by
        simp [r, inv_pow, mul_comm]
      _ ≤ r ^ n * ((T ^ 2) ^ n)⁻¹ :=
        mul_le_mul_of_nonneg_left hinvpow (pow_nonneg hrpos.le n)
      _ ≤ r ^ n * |D.det| :=
        mul_le_mul_of_nonneg_left hdetlower (pow_nonneg hrpos.le n)
      _ = |D.det| * r ^ n := by ring
  have hvolQformula : volume Qbox = ENNReal.ofReal (|D.det| * r ^ n) := by
    rw [hvolQ, hvolS, hvolC, ← ENNReal.ofReal_mul (abs_nonneg D.det)]
  have hQmeasure : volume Qbox ≤ volume P := measure_mono hQsub
  change ENNReal.ofReal
      (((n : ℝ) ^ n * B0 ^ (n ^ 2 * (n + 1)))⁻¹) ≤ volume P
  calc
    ENNReal.ofReal (((n : ℝ) ^ n * B0 ^ (n ^ 2 * (n + 1)))⁻¹) ≤
        ENNReal.ofReal (|D.det| * r ^ n) := ENNReal.ofReal_le_ofReal hreal
    _ = volume Qbox := hvolQformula.symm
    _ ≤ volume P := hQmeasure
