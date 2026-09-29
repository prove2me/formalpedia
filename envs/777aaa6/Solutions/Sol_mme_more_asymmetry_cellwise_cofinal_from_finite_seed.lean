-- Prove2me | solution 1 for mme_more_asymmetry_cellwise_cofinal_from_finite_seed
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:11:07.447246+00:00
-- url     : https://prove2.me/submissions/03a327c9-ff27-49b6-bddb-9676bda184db

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_child_matrix_data
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_mme_kronPow_kronPow_isomorphic
import Theorems.Thm_mme_restrict_kronPow

open BigOperators MME MME.TensorObj MME.HashExtraction
  MME.RecursiveYZ.Certificate Filter

set_option autoImplicit false
universe u

namespace C5Cofinal

/-- A constant `kronFin` family is a Kronecker power. -/
theorem kronFin_const {K : Type u} [Field K] {d : ℕ} (S : TensorObj K d) :
    ∀ n : ℕ, TensorObj.kronFin n (fun _ => S) = S.kronPow n
  | 0 => rfl
  | n + 1 => by
      show TensorObj.kron S (TensorObj.kronFin n (fun _ => S)) =
        TensorObj.kron S (S.kronPow n)
      rw [kronFin_const S n]

/-- Product over `Fin (n * f)` of a function of the second coordinate. -/
theorem prod_proj {M : Type*} [CommMonoid M] (n f : ℕ) (g : Fin f → M) :
    (∏ j : Fin (n * f), g (finProdFinEquiv.symm j).2) = (∏ i, g i) ^ n := by
  rw [← Equiv.prod_comp finProdFinEquiv (fun j => g (finProdFinEquiv.symm j).2)]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.prod_prod_type]
  simp [Finset.prod_const, Finset.card_univ]

/-- `u ^ n ≤ (1 + u) ^ n - 1` for `u ≥ 0`, `n ≥ 1`. -/
theorem pow_le_one_add_pow_sub_one (u : ℝ) (hu : 0 ≤ u) (n : ℕ) (hn : n ≠ 0) :
    u ^ n ≤ (u + 1) ^ n - 1 := by
  have := pow_add_pow_le hu zero_le_one hn
  simp only [one_pow] at this
  linarith

end C5Cofinal

open C5Cofinal in
theorem solution
    {K : Type u} [Field K]
    (hseed :
      ∃ (D : Data) (A : ∀ j, Stage ((D.hash j)))
    (hraw : MoreAsymmetryRawSourceCompatibility D A K)
    (M : ∀ j, (A j).ChildMM K),
    (∏ j, (M j).dimA) = D.a ∧
    (∏ j, (M j).dimB) = D.b ∧
    (∏ j, (M j).dimC) = D.c ∧
    (∀ j, ((8 ^ (A j).repairExponent : ℕ) : ℝ) ≤ (D.hash j).lower) ∧
    (∏ j, 2 * 8 ^ (A j).repairExponent) ≤ D.repairCopies ∧
    (∀ j, (A j).Budget) ∧
    0 < D.power ∧
    (2401 : ℝ) ^ (6 * D.power) <
      D.rate ((3952233 : ℝ) / 5000000)) :
    ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j))
    (V : ℝ) (error : ℕ → ℝ),
    (2401 : ℝ) < V ∧
    Tendsto (fun n ↦ (D n).power) atTop atTop ∧
    Tendsto error atTop (nhds 0) ∧
    ∀ᶠ n : ℕ in atTop,
      ∃ hraw : MoreAsymmetryRawSourceCompatibility (D n) (A n) K,
        ∃ M : ∀ j, (A n j).ChildMM K,
          (∏ j, (M j).dimA) = (D n).a ∧
          (∏ j, (M j).dimB) = (D n).b ∧
          (∏ j, (M j).dimC) = (D n).c ∧
          (∀ j, ((8 ^ (A n j).repairExponent : ℕ) : ℝ) ≤
            ((D n).hash j).lower) ∧
          (∏ j, 2 * 8 ^ (A n j).repairExponent) ≤ (D n).repairCopies ∧
          (∀ j, (A n j).Budget) ∧
          (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
            (D n).rate ((3952233 : ℝ) / 5000000) := by
  obtain ⟨D, A, hraw, M, hA, hB, hC, hlow, hrep, hbud, hpow, hrate⟩ := hseed
  set f := D.factors with hf
  -- the `n`-fold repetition of the seed
  let proj : ∀ n : ℕ, Fin (n * f) → Fin D.factors := fun n j => (finProdFinEquiv.symm j).2
  let Dn : ℕ → Data := fun n =>
    { factors := n * f
      hash := fun j => D.hash (proj n j)
      repairCopies := D.repairCopies ^ n
      repair_pos := pow_pos D.repair_pos n
      a := D.a ^ n
      b := D.b ^ n
      c := D.c ^ n
      power := n * D.power }
  let An : ∀ n j, Stage ((Dn n).hash j) := fun n j => A (proj n j)
  set tau : ℝ := (3952233 : ℝ) / 5000000 with htau
  set L : ℝ := (∏ j, (D.hash j).lower) / D.repairCopies with hL
  set Z : ℝ := (((D.a * D.b * D.c : ℕ) : ℝ) ^ tau) with hZ
  have hrateD : D.rate tau = (L - 1) * Z := rfl
  set Y : ℝ := (L - 1) * Z with hY
  have hZ0 : 0 ≤ Z := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2401 : (0 : ℝ) < 2401 ^ (6 * D.power) := by positivity
  have hYpos : 0 < Y := lt_trans h2401 (hrateD ▸ hrate)
  have hL1 : 0 ≤ L - 1 := by
    by_contra hneg
    push_neg at hneg
    have : Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le hZ0
    linarith
  have h6p : (6 * D.power : ℕ) ≠ 0 := by omega
  have h6pR : (0 : ℝ) < ((6 * D.power : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h6p
  set V : ℝ := Y ^ (((6 * D.power : ℕ) : ℝ)⁻¹) with hV
  have hV0 : 0 ≤ V := Real.rpow_nonneg hYpos.le _
  have hVpow : V ^ (6 * D.power) = Y := Real.rpow_inv_natCast_pow hYpos.le h6p
  refine ⟨Dn, An, V, fun _ => 0, ?_, ?_, tendsto_const_nhds, ?_⟩
  · -- 2401 < V
    rw [hV, Real.lt_rpow_inv_iff_of_pos (by norm_num) hYpos.le h6pR, Real.rpow_natCast]
    exact hrateD ▸ hrate
  · -- the power diverges
    show Tendsto (fun n => n * D.power) atTop atTop
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    exact Nat.le_mul_of_pos_right n hpow
  · refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hn0 : n ≠ 0 := by omega
    -- source compatibility
    have hiso : TensorObj.Isomorphic
        (TensorObj.kronFin (n * f) (fun _ : Fin (n * f) => hraw.source))
        ((sixSymmetrization (MME.StothersFourth.cwFourthObj K 5)).kronPow (n * D.power)) := by
      have h0 := hraw.ambient_isomorphic
      rw [kronFin_const] at h0
      rw [kronFin_const]
      refine TensorObj.Isomorphic.trans
        (mme_kronPow_kronPow_isomorphic hraw.source f n).symm ?_
      refine TensorObj.Isomorphic.trans ?_
        (mme_kronPow_kronPow_isomorphic _ D.power n)
      exact ⟨mme_restrict_kronPow h0.1 n, mme_restrict_kronPow h0.2 n⟩
    let hrawn : MoreAsymmetryRawSourceCompatibility (Dn n) (An n) K :=
      { source := hraw.source
        factor_restrict := fun j => hraw.factor_restrict (proj n j)
        ambient_isomorphic := hiso }
    let Mn : ∀ j, (An n j).ChildMM K := fun j => M (proj n j)
    refine ⟨hrawn, Mn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (∏ j : Fin (n * f), (M (finProdFinEquiv.symm j).2).dimA) = D.a ^ n
      rw [prod_proj n f (fun i => (M i).dimA), hA]
    · show (∏ j : Fin (n * f), (M (finProdFinEquiv.symm j).2).dimB) = D.b ^ n
      rw [prod_proj n f (fun i => (M i).dimB), hB]
    · show (∏ j : Fin (n * f), (M (finProdFinEquiv.symm j).2).dimC) = D.c ^ n
      rw [prod_proj n f (fun i => (M i).dimC), hC]
    · intro j
      exact hlow (proj n j)
    · show (∏ j : Fin (n * f), 2 * 8 ^ (A (finProdFinEquiv.symm j).2).repairExponent) ≤
        D.repairCopies ^ n
      rw [prod_proj n f (fun i => 2 * 8 ^ (A i).repairExponent)]
      exact Nat.pow_le_pow_left hrep n
    · intro j
      exact hbud (proj n j)
    · -- the rate
      have hlowprod : (∏ j : Fin (n * f), (D.hash (finProdFinEquiv.symm j).2).lower) =
          (∏ j, (D.hash j).lower) ^ n := prod_proj n f (fun i => (D.hash i).lower)
      have hRpos : (0 : ℝ) < D.repairCopies := by exact_mod_cast D.repair_pos
      have hrn : (Dn n).rate tau = (L ^ n - 1) * Z ^ n := by
        show ((∏ j : Fin (n * f), (D.hash (finProdFinEquiv.symm j).2).lower) /
            ((D.repairCopies ^ n : ℕ) : ℝ) - 1) *
            (((D.a ^ n * D.b ^ n * D.c ^ n : ℕ) : ℝ) ^ tau) = _
        rw [hlowprod, hL, div_pow, Nat.cast_pow]
        congr 1
        rw [hZ, ← mul_pow, ← mul_pow, Nat.cast_pow,
          ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
          ← Real.rpow_mul (Nat.cast_nonneg _)]
        congr 1; ring
      rw [hrn]
      show (V ^ 6) ^ (n * D.power) * (1 - 0) ≤ (L ^ n - 1) * Z ^ n
      have hVY : (V ^ 6) ^ (n * D.power) = Y ^ n := by
        rw [← pow_mul, show 6 * (n * D.power) = (6 * D.power) * n by ring, pow_mul, hVpow]
      rw [sub_zero, mul_one, hVY, hY, mul_pow]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hZ0 n)
      have := pow_le_one_add_pow_sub_one (L - 1) hL1 n hn0
      simpa using this
