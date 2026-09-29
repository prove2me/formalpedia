-- Prove2me | solution 1 for even2n_schatten_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-25T03:15:01.702028+00:00
-- url     : https://prove2.me/submissions/23fd0169-4cfd-4077-b547-5ae7edfc1565

import Definitions.Def_matrix_completion_gram_schatten
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Tactic.Positivity
import Theorems.Thm_schatten_norm_even_pow_eq_trace_row_gram_pow
import Theorems.Thm_trace_dilation_even_pow
import Theorems.Thm_general_rademacher_matrix_2p_trace_moment_general_index
import Theorems.Thm_engine_rhs_root_le

open Matrix MatrixCompletion
open scoped BigOperators

/-! ## Vendored internal block machinery (helper defs/lemmas; not platform vocabulary). -/

noncomputable def dilation {n1 n2 : ℕ} (S : Matrix (Fin n1) (Fin n2) ℝ) :
    Matrix (Fin n1 ⊕ Fin n2) (Fin n1 ⊕ Fin n2) ℝ :=
  Matrix.fromBlocks 0 S Sᵀ 0

noncomputable def coordScaled {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (c : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  fun i j => if (i, j) = c then p⁻¹ * (if c ∈ Omega then X c.1 c.2 else 0) else 0

noncomputable def coordVal {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (c : Fin n1 × Fin n2) : ℝ :=
  p⁻¹ * (if c ∈ Omega then X c.1 c.2 else 0)

noncomputable def rowEnergyVec {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    Fin n1 → ℝ :=
  fun i => ∑ j : Fin n2, (coordVal Omega p X (i, j)) ^ 2

noncomputable def colEnergyVec {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    Fin n2 → ℝ :=
  fun j => ∑ i : Fin n1, (coordVal Omega p X (i, j)) ^ 2

private lemma dilation_sq {n1 n2 : ℕ} (S : Matrix (Fin n1) (Fin n2) ℝ) :
    (dilation S) ^ 2 = Matrix.fromBlocks (S * Sᵀ) 0 0 (Sᵀ * S) := by
  rw [pow_two, dilation, Matrix.fromBlocks_multiply]; simp

private lemma coordScaled_mul_transpose {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) :
    (coordScaled Omega p X c) * (coordScaled Omega p X c)ᵀ
      = fun i i' => if i = c.1 ∧ i' = c.1 then (coordVal Omega p X c) ^ 2 else 0 := by
  classical
  funext i i'
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hcs : ∀ a b, coordScaled Omega p X c a b
      = if (a, b) = c then coordVal Omega p X c else 0 := by intro a b; rfl
  simp only [hcs]
  rw [Finset.sum_eq_single c.2]
  · simp only [show ((i, c.2) = c) ↔ (i = c.1) by rw [Prod.ext_iff]; simp,
               show ((i', c.2) = c) ↔ (i' = c.1) by rw [Prod.ext_iff]; simp]
    by_cases h1 : i = c.1 <;> by_cases h2 : i' = c.1 <;> simp [h1, h2, sq]
  · intro b _ hb
    rw [if_neg (fun h => hb (Prod.ext_iff.mp h).2)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma sum_coordScaled_mul_transpose {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    (∑ c : Fin n1 × Fin n2, (coordScaled Omega p X c) * (coordScaled Omega p X c)ᵀ)
      = Matrix.diagonal (rowEnergyVec Omega p X) := by
  classical
  funext i i'
  rw [Matrix.sum_apply]
  simp only [coordScaled_mul_transpose, Matrix.diagonal]
  by_cases hii : i = i'
  · subst hii
    simp only [Matrix.of_apply, if_pos rfl]
    rw [rowEnergyVec, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl (fun b _ => ?_); simp
    · intro a _ ha
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [if_neg]; rintro ⟨h1, _⟩; exact ha h1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [Matrix.of_apply, if_neg hii]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [if_neg]; rintro ⟨h1, h2⟩; exact hii (h1.trans h2.symm)

private lemma transpose_mul_coordScaled {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) :
    (coordScaled Omega p X c)ᵀ * (coordScaled Omega p X c)
      = fun j j' => if j = c.2 ∧ j' = c.2 then (coordVal Omega p X c) ^ 2 else 0 := by
  classical
  funext j j'
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hcs : ∀ a b, coordScaled Omega p X c a b
      = if (a, b) = c then coordVal Omega p X c else 0 := fun a b => rfl
  simp only [hcs]
  rw [Finset.sum_eq_single c.1]
  · simp only [show ((c.1, j) = c) ↔ (j = c.2) by rw [Prod.ext_iff]; simp,
               show ((c.1, j') = c) ↔ (j' = c.2) by rw [Prod.ext_iff]; simp]
    by_cases h1 : j = c.2 <;> by_cases h2 : j' = c.2 <;> simp [h1, h2, sq]
  · intro a _ ha
    rw [if_neg (fun h => ha (Prod.ext_iff.mp h).1)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma sum_transpose_mul_coordScaled {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    (∑ c : Fin n1 × Fin n2, (coordScaled Omega p X c)ᵀ * (coordScaled Omega p X c))
      = Matrix.diagonal (colEnergyVec Omega p X) := by
  classical
  funext j j'
  rw [Matrix.sum_apply]
  simp only [transpose_mul_coordScaled, Matrix.diagonal]
  by_cases hjj : j = j'
  · subst hjj
    simp only [Matrix.of_apply, if_pos rfl, colEnergyVec]
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl (fun a _ => ?_); simp
    · intro b _ hb
      refine Finset.sum_eq_zero (fun a _ => ?_)
      rw [if_neg]; rintro ⟨h1, _⟩; exact hb h1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [Matrix.of_apply, if_neg hjj]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [if_neg]; rintro ⟨h1, h2⟩; exact hjj (h1.trans h2.symm)

private lemma sum_dilation_coordScaled_sq_eq_blockdiag {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    (∑ c : Fin n1 × Fin n2, (dilation (coordScaled Omega p X c)) ^ 2)
      = Matrix.fromBlocks (Matrix.diagonal (rowEnergyVec Omega p X)) 0 0
          (Matrix.diagonal (colEnergyVec Omega p X)) := by
  classical
  simp only [dilation_sq]
  rw [← sum_coordScaled_mul_transpose, ← sum_transpose_mul_coordScaled]
  funext x y
  rw [Matrix.sum_apply]
  cases x with
  | inl i => cases y with
    | inl i' => simp [Matrix.fromBlocks_apply₁₁, Matrix.sum_apply]
    | inr j' => simp [Matrix.fromBlocks_apply₁₂]
  | inr j => cases y with
    | inl i' => simp [Matrix.fromBlocks_apply₂₁]
    | inr j' => simp [Matrix.fromBlocks_apply₂₂, Matrix.sum_apply]

private lemma rSM_eq_signed_sum {n1 n2 : Nat}
    (Omega eps : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) :
    rademacherSampledMatrix Omega eps p X
      = ∑ c : Fin n1 × Fin n2, rademacherSign eps c.1 c.2 • coordScaled Omega p X c := by
  classical
  funext i j
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · simp only [coordScaled, rademacherSampledMatrix, rademacherSign, Matrix.smul_apply,
      smul_eq_mul]
    by_cases hO : (i, j) ∈ Omega
    · rw [if_pos hO, if_pos hO, if_true]; ring
    · rw [if_neg hO, if_neg hO]; simp
  · intro c _ hc
    simp only [coordScaled, Matrix.smul_apply, smul_eq_mul]
    rw [if_neg (by exact fun h => hc (by rw [← h]))]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma engine_lhs_eq_rademacherExpectation {n1 n2 : Nat} {μ : Type*}
    [Fintype μ] [DecidableEq μ]
    (H : (Fin n1 × Fin n2) → Matrix μ μ ℝ) (p : Nat) :
    (∑ eps : Finset (Fin n1 × Fin n2),
        ((1 : ℝ) / 2) ^ (Fintype.card (Fin n1 × Fin n2))
          * Matrix.trace ((∑ c : Fin n1 × Fin n2,
              (if c ∈ eps then (1 : ℝ) else -1) • H c) ^ (2 * p)))
      = rademacherExpectation
          (fun eps => Matrix.trace ((∑ c : Fin n1 × Fin n2,
              rademacherSign eps c.1 c.2 • H c) ^ (2 * p))) := by
  unfold rademacherExpectation rademacherObservationWeight rademacherSign
  rfl

private lemma diagonal_quadratic_form_le {n : ℕ} (d : Fin n → ℝ) (B : ℝ)
    (hd : ∀ k, d k ≤ B) (hv : ∀ k, (0:ℝ) ≤ d k) (v : Fin n → ℝ) :
    (star v ⬝ᵥ (diagonal d) *ᵥ v) ≤ B * (star v ⬝ᵥ v) := by
  classical
  have hL : (star v ⬝ᵥ (diagonal d) *ᵥ v) = ∑ k, d k * (v k * v k) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mulVec_diagonal]; simp [Pi.star_apply, star_trivial]; ring
  have hR : B * (star v ⬝ᵥ v) = ∑ k, B * (v k * v k) := by
    rw [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [Pi.star_apply, star_trivial]
  rw [hL, hR]
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact mul_le_mul_of_nonneg_right (hd k) (mul_self_nonneg _)

private lemma block_diagonal_quadratic_form_le {n1 n2 : ℕ}
    (a : Fin n1 → ℝ) (b : Fin n2 → ℝ) (B : ℝ)
    (ha : ∀ i, a i ≤ B) (hb : ∀ j, b j ≤ B)
    (ha0 : ∀ i, (0:ℝ) ≤ a i) (hb0 : ∀ j, (0:ℝ) ≤ b j)
    (w : Fin n1 ⊕ Fin n2 → ℝ) :
    (star w ⬝ᵥ (Matrix.fromBlocks (diagonal a) 0 0 (diagonal b)) *ᵥ w)
      ≤ B * (star w ⬝ᵥ w) := by
  classical
  set v1 : Fin n1 → ℝ := fun i => w (Sum.inl i) with hv1
  set v2 : Fin n2 → ℝ := fun j => w (Sum.inr j) with hv2
  have hmv : (Matrix.fromBlocks (diagonal a) 0 0 (diagonal b)) *ᵥ w
      = Sum.elim ((diagonal a) *ᵥ v1) ((diagonal b) *ᵥ v2) := by
    rw [fromBlocks_mulVec]; simp only [Matrix.zero_mulVec, add_zero, zero_add]; rfl
  rw [hmv]
  have hsplit : (star w ⬝ᵥ Sum.elim ((diagonal a) *ᵥ v1) ((diagonal b) *ᵥ v2))
      = (star v1 ⬝ᵥ (diagonal a) *ᵥ v1) + (star v2 ⬝ᵥ (diagonal b) *ᵥ v2) := by
    rw [dotProduct, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.star_apply, hv1, hv2]; rfl
  have hww : (star w ⬝ᵥ w) = (star v1 ⬝ᵥ v1) + (star v2 ⬝ᵥ v2) := by
    rw [dotProduct, Fintype.sum_sum_type]
    simp only [Pi.star_apply, hv1, hv2]; rfl
  rw [hsplit, hww, mul_add]
  have h1 := diagonal_quadratic_form_le a B ha ha0 v1
  have h2 := diagonal_quadratic_form_le b B hb hb0 v2
  linarith

private lemma dilation_add {n1 n2 : ℕ} (A B : Matrix (Fin n1) (Fin n2) ℝ) :
    dilation (A + B) = dilation A + dilation B := by
  classical
  funext x y
  cases x with
  | inl i => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₁₁]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₁₂]
  | inr j => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₂₂]

private lemma dilation_smul {n1 n2 : ℕ} (s : ℝ) (A : Matrix (Fin n1) (Fin n2) ℝ) :
    dilation (s • A) = s • dilation A := by
  classical
  funext x y
  cases x with
  | inl i => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₁₁]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₁₂]
  | inr j => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₂₂]

private lemma dilation_sum {n1 n2 : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin n1) (Fin n2) ℝ) :
    dilation (∑ c ∈ s, f c) = ∑ c ∈ s, dilation (f c) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; funext x y; cases x <;> cases y <;> simp [dilation, Matrix.fromBlocks]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dilation_add, ih]

private lemma dilation_isHermitian {n1 n2 : ℕ} (A : Matrix (Fin n1) (Fin n2) ℝ) :
    (dilation A).IsHermitian := by
  classical
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  funext x y
  cases x with
  | inl i => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₁₁, Matrix.transpose_apply]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
                  Matrix.transpose_apply]
  | inr j => cases y with
    | inl i' => simp [dilation, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₁₂,
                  Matrix.transpose_apply]
    | inr j' => simp [dilation, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]

/-- D1-link with the platform `schattenNorm`, inlined from the two imported children
(`schatten_norm_even_pow_eq_trace_row_gram_pow` 197d0150 + `trace_dilation_even_pow` 68317d2d). -/
private lemma schatten_even_pow_le_trace_dilation_even_pow
    (n : Nat) (hn : 1 ≤ n) {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    schattenNorm (2 * n) X ^ (2 * n) ≤ Matrix.trace ((dilation X) ^ (2 * n)) := by
  rw [schatten_norm_even_pow_eq_trace_row_gram_pow n hn X]
  show _ ≤ Matrix.trace ((Matrix.fromBlocks 0 X Xᵀ 0) ^ (2 * n))
  rw [trace_dilation_even_pow]
  have hPSD : (Xᵀ * X).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self X
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hnn : 0 ≤ Matrix.trace ((Xᵀ * X) ^ n) := (hPSD.pow n).trace_nonneg
  have hkey : Matrix.trace ((X * X.transpose) ^ n)
      ≤ Matrix.trace ((X * X.transpose) ^ n) + Matrix.trace ((Xᵀ * X) ^ n) := by linarith
  simpa using hkey

/-! ## Energy discharge helpers (rowEnergyVec/colEnergyVec ≤ variance-scale²). -/

private lemma rowEnergyMax_nonneg {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    0 ≤ sampledRowEnergyMax Omega X := by
  unfold sampledRowEnergyMax
  rcases isEmpty_or_nonempty (Fin n1) with h | h
  · rw [Real.iSup_of_isEmpty]
  · exact Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => by positivity))

private lemma colEnergyMax_nonneg {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    0 ≤ sampledColumnEnergyMax Omega X := by
  unfold sampledColumnEnergyMax
  rcases isEmpty_or_nonempty (Fin n2) with h | h
  · rw [Real.iSup_of_isEmpty]
  · exact Real.iSup_nonneg (fun j => Finset.sum_nonneg (fun i _ => by positivity))

/-- `rowEnergyVec Ω p X i = p⁻² · ∑_j δ_ij X_ij²`. -/
private lemma rowEnergyVec_eq {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) (i : Fin n1) :
    rowEnergyVec Omega p X i
      = (p⁻¹)^2 * ∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0 := by
  rw [rowEnergyVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [coordVal]
  by_cases h : (i, j) ∈ Omega
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

private lemma colEnergyVec_eq {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) (j : Fin n2) :
    colEnergyVec Omega p X j
      = (p⁻¹)^2 * ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0 := by
  rw [colEnergyVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coordVal]
  by_cases h : (i, j) ∈ Omega
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

/-! ## MAIN: even-2n Schatten moment bound (variance-scale RHS, platform vocabulary). -/

theorem solution {n1 n2 : Nat} (n : Nat) (hn : 1 ≤ n)
    (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (hd1 : 1 ≤ (n1 + n2)) (hlog : Real.log ((n1 + n2 : ℕ)) ≤ (2 * n : ℕ)) :
    rademacherExpectation (fun eps =>
        schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1
          * rademacherSampledVarianceScale Omega p X) ^ (2 * n) := by
  classical
  -- variance scale and its square as the eigenvalue bound B
  set emax : ℝ := max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) with hemax
  have hemax0 : 0 ≤ emax := le_max_of_le_left (rowEnergyMax_nonneg Omega X)
  set B : ℝ := (p⁻¹)^2 * emax with hBdef
  have hpinv2 : 0 ≤ (p⁻¹)^2 := sq_nonneg _
  have hB0 : 0 ≤ B := by rw [hBdef]; exact mul_nonneg hpinv2 hemax0
  have hrsvs : rademacherSampledVarianceScale Omega p X = p⁻¹ * Real.sqrt emax := by
    unfold rademacherSampledVarianceScale; rw [hemax]
  -- final even-power identity: (√(2n)·e·√B)^(2n) = (√(2n)·e·rsvs)^(2n)
  -- (since √B = |p⁻¹|·√emax and rsvs = p⁻¹·√emax differ only by the sign of p⁻¹,
  --  killed by the even exponent 2n)
  have hfinalEq : (Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt B) ^ (2 * n)
      = (Real.sqrt (2 * n : ℕ) * Real.exp 1
          * rademacherSampledVarianceScale Omega p X) ^ (2 * n) := by
    have hAnn : (0:ℝ) ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 := by positivity
    have heven : Even (2 * n) := ⟨n, by ring⟩
    rw [hBdef, hrsvs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    -- both sides equal |√(2n)·e·p⁻¹·√emax|^(2n)
    rw [show Real.sqrt (2 * n : ℕ) * Real.exp 1 * (|p⁻¹| * Real.sqrt emax)
          = |Real.sqrt (2 * n : ℕ) * Real.exp 1 * (p⁻¹ * Real.sqrt emax)| by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (2 * n : ℕ)),
          abs_of_nonneg (le_of_lt (Real.exp_pos 1)), abs_of_nonneg (Real.sqrt_nonneg emax)]]
    rw [heven.pow_abs]
  -- energy discharge: rowEnergyVec i ≤ B, colEnergyVec j ≤ B, and ≥ 0
  have hrow0 : ∀ i, 0 ≤ rowEnergyVec Omega p X i := fun i =>
    Finset.sum_nonneg (fun j _ => by positivity)
  have hcol0 : ∀ j, 0 ≤ colEnergyVec Omega p X j := fun j =>
    Finset.sum_nonneg (fun i _ => by positivity)
  have hrow : ∀ i, rowEnergyVec Omega p X i ≤ B := by
    intro i
    rw [rowEnergyVec_eq, hBdef]
    apply mul_le_mul_of_nonneg_left _ hpinv2
    refine le_trans ?_ (le_max_left _ _)
    unfold sampledRowEnergyMax
    exact le_ciSup (f := fun i => ∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)
      (Finite.bddAbove_range _) i
  have hcol : ∀ j, colEnergyVec Omega p X j ≤ B := by
    intro j
    rw [colEnergyVec_eq, hBdef]
    apply mul_le_mul_of_nonneg_left _ hpinv2
    refine le_trans ?_ (le_max_right _ _)
    unfold sampledColumnEnergyMax
    exact le_ciSup (f := fun j => ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)
      (Finite.bddAbove_range _) j
  -- The Hermitian family used by the engine: H c = dilation (coordScaled c) over Fin n1 ⊕ Fin n2.
  set H : (Fin n1 × Fin n2) → Matrix (Fin n1 ⊕ Fin n2) (Fin n1 ⊕ Fin n2) ℝ :=
    fun c => dilation (coordScaled Omega p X c) with hHdef
  have hHerm : ∀ c, (H c).IsHermitian := fun c => dilation_isHermitian _
  have hVeq : (∑ c : Fin n1 × Fin n2, H c * H c)
      = Matrix.fromBlocks (Matrix.diagonal (rowEnergyVec Omega p X)) 0 0
          (Matrix.diagonal (colEnergyVec Omega p X)) := by
    have hsq : ∀ c, H c * H c = (dilation (coordScaled Omega p X c)) ^ 2 := by
      intro c; rw [hHdef, pow_two]
    simp_rw [hsq]
    exact sum_dilation_coordScaled_sq_eq_blockdiag Omega p X
  have hVHerm : (∑ c : Fin n1 × Fin n2, H c * H c).IsHermitian := by
    rw [hVeq]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.fromBlocks_transpose, Matrix.diagonal_transpose, Matrix.diagonal_transpose,
        Matrix.transpose_zero, Matrix.transpose_zero]
  -- quadratic-form bound for V = ∑ H c * H c
  have hquad : ∀ w : (Fin n1 ⊕ Fin n2) → ℝ,
      (star w ⬝ᵥ (∑ c : Fin n1 × Fin n2, H c * H c) *ᵥ w) ≤ B * (star w ⬝ᵥ w) := by
    intro w
    rw [hVeq]
    exact block_diagonal_quadratic_form_le (rowEnergyVec Omega p X)
      (colEnergyVec Omega p X) B hrow hcol hrow0 hcol0 w
  -- ENGINE (general-index, quadratic-form form)
  have hcardμ : (Fintype.card (Fin n1 ⊕ Fin n2) : ℝ) = (n1 + n2 : ℕ) := by
    simp [Fintype.card_sum]
  have hEngine := general_rademacher_matrix_2p_trace_moment_general_index
    H hHerm B hB0 hVHerm hquad n
  rw [hcardμ] at hEngine
  have hLHSeq := engine_lhs_eq_rademacherExpectation H n
  rw [hLHSeq] at hEngine
  -- dilation(rSM eps) = ∑ c, sign • H c
  have hdilrSM : ∀ eps : Finset (Fin n1 × Fin n2),
      dilation (rademacherSampledMatrix Omega eps p X)
        = ∑ c : Fin n1 × Fin n2, rademacherSign eps c.1 c.2 • H c := by
    intro eps
    rw [rSM_eq_signed_sum Omega eps p X, dilation_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [dilation_smul]
  -- Monotone-expectation chain
  have hchain :
      rademacherExpectation (fun eps =>
          schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
        ≤ ((Nat.factorial (2*n):ℝ)/((2^n:ℝ)*(Nat.factorial n:ℝ))) * B^n * (n1 + n2 : ℕ) := by
    refine le_trans ?_ hEngine
    unfold rademacherExpectation
    refine Finset.sum_le_sum (fun eps _ => ?_)
    have hw0 : (0:ℝ) ≤ rademacherObservationWeight eps := by
      unfold rademacherObservationWeight; positivity
    apply mul_le_mul_of_nonneg_left _ hw0
    dsimp only
    have hd1' := schatten_even_pow_le_trace_dilation_even_pow n hn
      (rademacherSampledMatrix Omega eps p X)
    rw [← hdilrSM eps]
    exact hd1'
  -- engine RHS root bound
  set Y : ℝ := ((Nat.factorial (2*n):ℝ)/((2^n:ℝ)*(Nat.factorial n:ℝ))) * B^n * (n1 + n2 : ℕ)
    with hYdef
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hroot := engine_rhs_root_le n (n1 + n2) hn hd1 B hB0 (by
    push_cast at hlog ⊢; convert hlog using 2 <;> push_cast <;> ring)
  have hRHS_nn : (0:ℝ) ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt B := by positivity
  have h2nne : (2 * n) ≠ 0 := by positivity
  have hroundtrip : (Real.rpow Y ((1:ℝ)/(2*n))) ^ (2 * n) = Y := by
    have hexp : (1:ℝ)/(2 * n) = ((2 * n : ℕ):ℝ)⁻¹ := by push_cast; rw [one_div]
    rw [hexp]; exact Real.rpow_inv_natCast_pow hY0 h2nne
  have hpow : (Real.rpow Y ((1:ℝ)/(2*n))) ^ (2 * n)
      ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt B) ^ (2 * n) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hY0 _) hroot (2 * n)
  rw [hroundtrip] at hpow
  -- combine; rewrite √B = variance scale
  calc rademacherExpectation (fun eps =>
          schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      ≤ Y := hchain
    _ ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt B) ^ (2 * n) := hpow
    _ = (Real.sqrt (2 * n : ℕ) * Real.exp 1
          * rademacherSampledVarianceScale Omega p X) ^ (2 * n) := hfinalEq

#print axioms solution
