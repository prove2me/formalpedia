-- Prove2me | solution 1 for mme_complete_split_exact_power_six_finite_witness_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T14:30:11.037897+00:00
-- url     : https://prove2.me/submissions/65fcf944-78c4-4bdd-be79-3d23f5b5b00e

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_complete_split_exact_power_concatenation_restrict
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_bigAdd_MM_kronPow_tau_flatten
import Theorems.Thm_mme_restrict_kronPow
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict

open MME MME.CompleteSplit MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open BigOperators
open scoped NNReal

universe u

set_option autoImplicit false

/-!
# Repeating an exact complete-profile witness

A finite matrix extraction from the six-symmetrization of an exact complete-profile power at length
`N` is repeated `r` times to give one at length `N * r`, because the `r`-fold Kronecker power of the
exact power restricts from the exact power at the multiplied length.
-/

private theorem unit_restrict_exact_zero
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) :
    TensorObj.Restrict (TensorObj.oneObj : TensorObj K 3)
      (restrictedPower T b label beta 0 0) := by
  classical
  unfold restrictedPower
  refine mme_restrict_basisAllAllowedSubtensor_of_vanishes
    (T.kronPow 0) TensorObj.oneObj
    (fun i ↦ kronPowModeBasis T i (b i) 0)
    (fun i ↦ ApproxConsistent (label i) (beta i) 0)
    (fun _ ↦ LinearMap.id) ?_ ?_
  · exact LinearMap.congr_fun (PiTensorProduct.map_id (R := K)) _
  · intro i w hnot
    exfalso
    apply hnot
    intro sigma
    simp [wordCount]

private theorem repeat_from_concatenation
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (N r : ℕ) :
    TensorObj.Restrict ((restrictedPower T b label beta 0 N).kronPow r)
      (restrictedPower T b label beta 0 (N * r)) := by
  induction r with
  | zero =>
    simpa only [Nat.mul_zero] using unit_restrict_exact_zero T b label beta
  | succ r ih =>
    have hstep : TensorObj.Restrict
        (TensorObj.kron (restrictedPower T b label beta 0 N)
          ((restrictedPower T b label beta 0 N).kronPow r))
        (TensorObj.kron (restrictedPower T b label beta 0 N)
          (restrictedPower T b label beta 0 (N * r))) := by
      let P := tensorPreorder K
      change P.le
        (TensorQ.toQ (restrictedPower T b label beta 0 N) *
          TensorQ.toQ ((restrictedPower T b label beta 0 N).kronPow r))
        (TensorQ.toQ (restrictedPower T b label beta 0 N) *
          TensorQ.toQ (restrictedPower T b label beta 0 (N * r)))
      simpa only [mul_comm] using
        P.mul_right
          (TensorQ.toQ ((restrictedPower T b label beta 0 N).kronPow r))
          (TensorQ.toQ (restrictedPower T b label beta 0 (N * r))) ih
          (TensorQ.toQ (restrictedPower T b label beta 0 N))
    simpa only [Nat.mul_succ, Nat.add_comm] using
      hstep.trans (mme_complete_split_exact_power_concatenation_restrict
        T b label beta N (N * r))

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (N r : ℕ) (tau v : ℝ)
    (h : SixFiniteWitness TensorObj.Restrict
      (restrictedPower T b label beta 0 N) N tau v) :
    SixFiniteWitness TensorObj.Restrict
      (restrictedPower T b label beta 0 (N * r)) (N * r) tau v := by
  obtain ⟨k, a, b', c, hrestrict, hweight⟩ := h
  obtain ⟨q, A, B, C, hflatten, hweightPower⟩ :=
    mme_bigAdd_MM_kronPow_tau_flatten (K := K) a b' c tau (r := r)
  refine ⟨q, A, B, C, ?_, ?_⟩
  · exact hflatten.trans ((mme_restrict_kronPow hrestrict r).trans
      ((mme_sixSymmetrization_kronPow_isomorphic
        (restrictedPower T b label beta 0 N) r).1.trans
        (mme_sixSymmetrization_restrict
          (repeat_from_concatenation T b label beta N r))))
  · have hnonneg : 0 ≤ v ^ (6 * N) := by
      rw [show 6 * N = (3 * N) * 2 by omega, pow_mul]
      exact sq_nonneg _
    calc
      v ^ (6 * (N * r)) = (v ^ (6 * N)) ^ r := by
        rw [← pow_mul]
        congr 1
        ring
      _ ≤ (∑ i, (((a i * b' i * c i : ℕ) : ℝ) ^ tau)) ^ r :=
        pow_le_pow_left₀ hnonneg hweight r
      _ = ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := hweightPower.symm
