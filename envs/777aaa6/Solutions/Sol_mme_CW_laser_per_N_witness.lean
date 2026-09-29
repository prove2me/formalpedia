-- Prove2me | solution 1 for mme_CW_laser_per_N_witness
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T01:50:56.761277+00:00
-- url     : https://prove2.me/submissions/e63e41ca-b5ae-4267-8648-1df4942b490a

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_canonical_grading
import Definitions.Def_mme_CW_support_pattern
import Definitions.Def_mme_subrank_capacity_poly
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_tensor_rank
import Theorems.Thm_mme_CW_block_kronPow_MM_corrected
import Theorems.Thm_mme_CW_laser_per_N_witness

/-! # `Sol_mme_CW_laser_per_N_witness` — CW-specialized per-N witness.

Sorry-free closure of the CW-specific replacement for the under-specified
abstract leaf `mme_laser_per_N_witness`.

**Proof structure.**

The conjunction `(1 ≤ V) ∧ (∃ c, …)` splits naturally.

* **Left conjunct (`1 ≤ V`).** With `V = q^(1/3)` and `q ≥ 1`, this is
  `Real.one_le_rpow` applied to `(q : ℝ) ≥ 1` and `1/3 ≥ 0`.

* **Right conjunct (polynomial witness).** Take:
  - `c := 0` (polynomial degree zero — the witness has a single block).
  - For each `N`, `k := 1`, `a 0 = 1`, `b 0 = 1`, `c' 0 = q^N`.
  - The constant type-sequence `τ : Fin N → CWSupportPattern`,
    `τ k := (0, 1, 1)`. By the cwBlockMMDim table,
    `cwBlockMMDim (0, 1, 1) q = (1, 1, q)`, so the multinomial products
    are `(1, 1, q^N)`.
  - Apply `Sol_mme_CW_block_kronPow_MM_corrected.solution` at this `τ` to
    get `Restrict (MMObj K 1 1 (q^N)) ((CWObj K q).kronPow N)`.
  - `bigAdd (Fin 1)` of `MMObj K 1 1 (q^N)` reduces definitionally to
    `MMObj K 1 1 (q^N)` (by the `| 1 => f 0` case).
  - The Hölder bound: `V^N · (1 - ε) = q^(N/3) · (1 - ε) ≤ q^(N/3)`
    `= (1 · 1 · q^N)^(1/3) = ∑_{i : Fin 1} (a i · b i · c' i)^(1/3)`.
  - Use `Filter.frequently_atTop'` (any tail contains a value, so
    "for all N" implies "frequently N").

Axiom-clean: `propext, Classical.choice, Quot.sound` only. -/

open MME BigOperators Filter

universe u

namespace MMECWLaserPerNWitnessSol

variable {K : Type u} [Field K]

/-! ## (1) Left conjunct: `1 ≤ q^(1/3)`. -/

/-- For `q ≥ 1`, `1 ≤ q^(1/3)`. -/
private theorem one_le_q_rpow_third (q : ℕ) (hq : 1 ≤ q) :
    (1 : ℝ) ≤ ((q : ℝ)) ^ ((1 : ℝ) / 3) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h13 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  exact Real.one_le_rpow hq1 h13

/-! ## (2) Right conjunct: polynomial witness via constant τ at (0, 1, 1). -/

/-- The constant type sequence `τ : Fin N → CWSupportPattern` mapping every
position to `(0, 1, 1) : Fin 3 × Fin 3 × Fin 3`. -/
private def constTau (N : ℕ) : Fin N → Fin 3 × Fin 3 × Fin 3 :=
  fun _ => (0, 1, 1)

/-- `(0, 1, 1) ∈ CWSupportPattern`. -/
private lemma const_in_S : ((0 : Fin 3), (1 : Fin 3), (1 : Fin 3)) ∈ CWSupportPattern := by
  unfold CWSupportPattern
  simp

/-- The hypothesis "`constTau N k ∈ CWSupportPattern` for all k". -/
private lemma constTau_in_S (N : ℕ) :
    ∀ k : Fin N, constTau N k ∈ CWSupportPattern := by
  intro _
  exact const_in_S

/-- `cwBlockMMDim (0, 1, 1) q = (1, 1, q)`. -/
private lemma cwBlockMMDim_011 (q : ℕ) :
    cwBlockMMDim ((0 : Fin 3), (1 : Fin 3), (1 : Fin 3)) q = (1, 1, q) := by
  unfold cwBlockMMDim
  simp

/-- The product over `Fin N` of the first component of `cwBlockMMDim (constTau N k) q`
is `1`. -/
private lemma prod_const_first (q N : ℕ) :
    (∏ k : Fin N, (cwBlockMMDim (constTau N k) q).1) = 1 := by
  have h : ∀ k : Fin N, (cwBlockMMDim (constTau N k) q).1 = 1 := by
    intro k
    unfold constTau
    rw [cwBlockMMDim_011]
  rw [Finset.prod_congr rfl (fun k _ => h k)]
  simp

/-- The product over `Fin N` of the second component is also `1`. -/
private lemma prod_const_second (q N : ℕ) :
    (∏ k : Fin N, (cwBlockMMDim (constTau N k) q).2.1) = 1 := by
  have h : ∀ k : Fin N, (cwBlockMMDim (constTau N k) q).2.1 = 1 := by
    intro k
    unfold constTau
    rw [cwBlockMMDim_011]
  rw [Finset.prod_congr rfl (fun k _ => h k)]
  simp

/-- The product over `Fin N` of the third component is `q^N`. -/
private lemma prod_const_third (q N : ℕ) :
    (∏ k : Fin N, (cwBlockMMDim (constTau N k) q).2.2) = q ^ N := by
  have h : ∀ k : Fin N, (cwBlockMMDim (constTau N k) q).2.2 = q := by
    intro k
    unfold constTau
    rw [cwBlockMMDim_011]
  rw [Finset.prod_congr rfl (fun k _ => h k)]
  simp [Finset.prod_const]

/-- The CW kronPow MM Restrict instantiated at the constant `(0, 1, 1)`
type-sequence: `Restrict (MMObj K 1 1 (q^N)) ((CWObj K q).kronPow N)`.

Calls the (locally `sorry`-stubbed but Sol-closed) leaf
`mme_CW_block_kronPow_MM_corrected`. -/
private theorem const_τ_kronPow_Restrict (q N : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 (q^N)) ((CWObj K q).kronPow N) := by
  -- Apply mme_CW_block_kronPow_MM_corrected at the constant τ.
  have h := mme_CW_block_kronPow_MM_corrected (K := K) q N (constTau N) (constTau_in_S N)
  -- h : Restrict (MMObj K (∏ k, (cwBlockMMDim _).1) (...) (...)) ((CWObj K q).kronPow N)
  rw [prod_const_first, prod_const_second, prod_const_third] at h
  exact h

/-! ## (3) bigAdd-of-Fin-1 simplification. -/

/-- For any 3-tensor family `f : Fin 1 → TensorObj K 3`, `bigAdd f = f 0`
(definitional via the `| 1 => f 0` case of `bigAdd`). -/
private lemma bigAdd_fin_one {d : ℕ} (f : Fin 1 → TensorObj K d) :
    TensorObj.bigAdd f = f 0 := rfl

/-! ## (4) Hölder bound at the constant witness. -/

/-- `(1 · 1 · q^N : ℕ) = q^N`. -/
private lemma trip_prod_eq (q N : ℕ) :
    ((1 * 1 * q^N : ℕ) : ℝ) = ((q^N : ℕ) : ℝ) := by
  norm_num

/-- `((q^N : ℕ) : ℝ)^(1/3) = (q^(1/3))^N`. -/
private lemma qN_third_eq_V_pow_N (q N : ℕ) :
    ((q^N : ℕ) : ℝ) ^ ((1 : ℝ) / 3) = (((q : ℝ)) ^ ((1 : ℝ) / 3)) ^ N := by
  -- Step 1: ((q^N : ℕ) : ℝ) = (q : ℝ)^N
  have h1 : ((q^N : ℕ) : ℝ) = ((q : ℝ)) ^ N := by
    push_cast
    ring
  rw [h1]
  -- Step 2: ((q:ℝ)^N)^(1/3) = ((q:ℝ)^(1/3))^N
  -- Real.rpow_natCast and Real.rpow_mul / pow-rpow interchange.
  -- (q^N) ^ (1/3) = q^(N*(1/3)) = q^(N/3)
  -- (q^(1/3))^N = q^(N/3) similarly.
  have hq_nn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  rw [← Real.rpow_natCast ((q : ℝ)) N]
  rw [← Real.rpow_natCast (((q : ℝ)) ^ ((1 : ℝ) / 3)) N]
  rw [← Real.rpow_mul hq_nn]
  rw [← Real.rpow_mul hq_nn]
  congr 1
  ring

/-- The Hölder bound: for `q ≥ 1`, `ε > 0`, and `N : ℕ`,
`V^N · (1 - ε) ≤ ∑ (a · b · c')^(1/3)` with the chosen `(1, 1, q^N)` witness. -/
private theorem holder_bound_const (q N : ℕ) (_hq : 1 ≤ q) (ε : ℝ) (hε : 0 < ε) :
    (((q : ℝ)) ^ ((1 : ℝ) / 3)) ^ N * (1 - ε) ≤
      ∑ _i : Fin 1, ((1 * 1 * q^N : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
  -- LHS: V^N · (1-ε) ≤ V^N (since 1-ε ≤ 1 and V^N ≥ 0).
  -- RHS: ∑_{i : Fin 1} (q^N : ℝ)^(1/3) = (q^N : ℝ)^(1/3) = V^N.
  have hV_nn : 0 ≤ ((q : ℝ)) ^ ((1 : ℝ) / 3) := by
    have hq_nn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
    exact Real.rpow_nonneg hq_nn _
  have hVN_nn : 0 ≤ (((q : ℝ)) ^ ((1 : ℝ) / 3)) ^ N := pow_nonneg hV_nn _
  -- Sum over Fin 1 is just the value at 0.
  rw [Fin.sum_univ_one]
  -- Reduce to (1*1*q^N : ℕ:ℝ)^(1/3) = V^N.
  rw [trip_prod_eq]
  rw [qN_third_eq_V_pow_N]
  -- Now goal: V^N · (1-ε) ≤ V^N.
  have h1mε : 1 - ε ≤ 1 := by linarith
  calc (((q : ℝ)) ^ ((1 : ℝ) / 3)) ^ N * (1 - ε)
      ≤ (((q : ℝ)) ^ ((1 : ℝ) / 3)) ^ N * 1 := by
        exact mul_le_mul_of_nonneg_left h1mε hVN_nn
    _ = (((q : ℝ)) ^ ((1 : ℝ) / 3)) ^ N := by ring

/-! ## (5) Frequently-at-top via universal: for all N, the witness exists. -/

/-- For all N, the witness data `(k, a, b, c')` exists with the constant
choice. -/
private theorem witness_exists_at_N (q : ℕ) (hq : 1 ≤ q) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ (k : ℕ) (a b c' : Fin k → ℕ),
      (k : ℝ) ≤ ((N : ℝ) + 1) ^ (0 : ℝ) ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
        ((CWObj K q).kronPow N)
      ∧ (((q : ℝ)) ^ ((1 : ℝ) / 3)) ^ N * (1 - ε) ≤
          ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
  -- k := 1, a := constant 1, b := constant 1, c' := constant q^N.
  refine ⟨1, (fun _ => 1), (fun _ => 1), (fun _ => q^N), ?_, ?_, ?_⟩
  · -- (k:ℝ) = 1 ≤ (N+1)^0 = 1.
    have : ((N : ℝ) + 1) ^ (0 : ℝ) = 1 := by
      apply Real.rpow_zero
    rw [this]
    norm_num
  · -- bigAdd (Fin 1, MMObj K 1 1 (q^N)) = MMObj K 1 1 (q^N), Restricts to (CWObj q).kronPow N.
    rw [bigAdd_fin_one]
    exact const_τ_kronPow_Restrict (K := K) q N
  · -- Hölder bound.
    exact holder_bound_const q N hq ε hε

/-- The witness existential: for all ε > 0, frequently many N, the polynomial
witness exists. We use degree `c := 0`. -/
private theorem witness_existential (q : ℕ) (hq : 1 ≤ q) :
    ∃ c : ℝ,
      ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in atTop,
        ∃ (k : ℕ) (a b c' : Fin k → ℕ),
          (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
            ((CWObj K q).kronPow N)
          ∧ (((q : ℝ)) ^ ((1 : ℝ) / 3)) ^ N * (1 - ε) ≤
              ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
  refine ⟨0, ?_⟩
  intro ε hε
  -- "for all N, P N" implies "frequently P".
  apply Filter.Frequently.of_forall (p := fun N : ℕ =>
    ∃ (k : ℕ) (a b c' : Fin k → ℕ),
      (k : ℝ) ≤ ((N : ℝ) + 1) ^ (0 : ℝ) ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
        ((CWObj K q).kronPow N)
      ∧ (((q : ℝ)) ^ ((1 : ℝ) / 3)) ^ N * (1 - ε) ≤
          ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
  intro N
  exact witness_exists_at_N (K := K) q hq ε hε N

end MMECWLaserPerNWitnessSol

open MMECWLaserPerNWitnessSol

/-- **CW-specialized per-N polynomial-bounded laser-method witness — sorry-free.**

Closes `mme_CW_laser_per_N_witness` via the constant-τ instantiation:

* `1 ≤ V`: `Real.one_le_rpow` applied to `(q : ℝ) ≥ 1`.
* Witness: `k = 1`, `(a, b, c') = (1, 1, q^N)`, polynomial degree `c = 0`. -/
theorem solution {K : Type u} [Field K] (q : ℕ) (hq : 1 ≤ q) :
    let V : ℝ := ((q : ℝ)) ^ ((1 : ℝ) / 3)
    (1 ≤ V) ∧ ∃ c : ℝ,
      ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in atTop,
        ∃ (k : ℕ) (a b c' : Fin k → ℕ),
          (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
            ((CWObj K q).kronPow N)
          ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
  simp only
  refine ⟨?_, ?_⟩
  · exact one_le_q_rpow_third q hq
  · exact witness_existential (K := K) q hq
