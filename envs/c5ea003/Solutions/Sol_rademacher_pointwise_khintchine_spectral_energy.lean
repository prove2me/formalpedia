-- Prove2me | solution 1 for rademacher_pointwise_khintchine_spectral_energy
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-25T09:38:15.068676+00:00
-- url     : https://prove2.me/submissions/0f659b19-83d9-4461-bdef-58c3c31ac174

import Mathlib
import Definitions.Def_matrix_completion_gram_schatten
import Mathlib.Analysis.InnerProductSpace.Trace

/-! GENERALIZED Tropp engine (index D) + dilation + bridge. -/


open Matrix
open scoped BigOperators
open scoped MatrixOrder

-- ===== Fact 2.2 (Codex) =====


private lemma trace_mul_nonneg_of_posSemidef {D : Type*} [Fintype D] [DecidableEq D]
    {B A : Matrix D D ℝ} (hB : B.PosSemidef) (hA : A.PosSemidef) :
    0 ≤ Matrix.trace (B * A) := by
  classical
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [hX]
  have hXA : (X * A * Xᴴ).PosSemidef := hA.mul_mul_conjTranspose_same X
  have htrace : 0 ≤ Matrix.trace (X * A * Xᴴ) := hXA.trace_nonneg
  convert htrace using 1
  calc
    Matrix.trace ((star X * X) * A) = Matrix.trace ((Xᴴ * X) * A) := by
      rw [Matrix.star_eq_conjTranspose]
    _ = Matrix.trace (A * Xᴴ * X) := Matrix.trace_mul_cycle Xᴴ X A
    _ = Matrix.trace (X * A * Xᴴ) := Matrix.trace_mul_cycle A Xᴴ X

private lemma norm_smul_one_sub_posSemidef {D : Type*} [Fintype D] [DecidableEq D] {H : Matrix D D ℝ}
    (hH : H.IsHermitian) (normH : ℝ) (hnorm : ∀ i, hH.eigenvalues i ≤ normH) :
    (normH • (1 : Matrix D D ℝ) - H).PosSemidef := by
  classical
  let U : Matrix D D ℝ := hH.eigenvectorUnitary
  let Dm : Matrix D D ℝ := diagonal fun i => normH - hH.eigenvalues i
  have hD : Dm.PosSemidef := by
    dsimp [Dm]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hnorm i))
  have hUDU : (U * Dm * Uᴴ).PosSemidef := by
    simpa [U] using hD.mul_mul_conjTranspose_same U
  convert hUDU using 1
  dsimp [U, Dm]
  have hU : (↑hH.eigenvectorUnitary : Matrix D D ℝ) *
      (↑hH.eigenvectorUnitary : Matrix D D ℝ)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Unitary.coe_mul_star_self hH.eigenvectorUnitary)
  conv_lhs => rw [hH.spectral_theorem]
  rw [← hU]
  rw [← Matrix.smul_mul normH
    (↑hH.eigenvectorUnitary : Matrix D D ℝ)
    ((↑hH.eigenvectorUnitary : Matrix D D ℝ)ᴴ)]
  rw [Matrix.smul_eq_mul_diagonal
    (↑hH.eigenvectorUnitary : Matrix D D ℝ) normH]
  have hdiag :
      diagonal (fun i : D => normH - hH.eigenvalues i) =
        (diagonal (fun _ : D => normH) - diagonal hH.eigenvalues :
          Matrix D D ℝ) := by
    rw [diagonal_sub]
  simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rw [hdiag]
  noncomm_ring

theorem tropp_fact_2_2 {D : Type*} [Fintype D] [DecidableEq D] (H A : Matrix D D ℝ)
    (hH : H.IsHermitian) (hA : A.PosSemidef) (normH : ℝ)
    (hnorm : ∀ i, hH.eigenvalues i ≤ normH) :
    Matrix.trace (H * A) ≤ normH * Matrix.trace A := by
  classical
  let B : Matrix D D ℝ := normH • 1 - H
  have hB : B.PosSemidef := by
    simpa [B] using norm_smul_one_sub_posSemidef hH normH hnorm
  have hnonneg : 0 ≤ Matrix.trace (B * A) :=
    trace_mul_nonneg_of_posSemidef hB hA
  have htrace : 0 ≤ normH * Matrix.trace A - Matrix.trace (H * A) := by
    simpa [B, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_smul] using hnonneg
  linarith

-- ===== Fact 2.4 (Codex) =====



lemma scalar_bound (lam mu : ℝ) (r q : ℕ) (hq : q ≤ 2 * r) :
    lam ^ q * mu ^ (2 * r - q) + lam ^ (2 * r - q) * mu ^ q
      ≤ lam ^ (2 * r) + mu ^ (2 * r) := by
  let p := 2 * r - q
  change lam ^ q * mu ^ p + lam ^ p * mu ^ q ≤ lam ^ (2 * r) + mu ^ (2 * r)
  have hpq : q + p = 2 * r := by
    dsimp [p]
    exact Nat.add_sub_of_le hq
  have hpar : Even p ↔ Even q := by
    dsimp [p]
    rw [Nat.even_sub hq]
    have h2r : Even (2 * r) := even_two_mul r
    simp [h2r]
  have hprod : 0 ≤ (lam ^ q - mu ^ q) * (lam ^ p - mu ^ p) := by
    rcases Nat.even_or_odd q with hqe | hqo
    · have hpe : Even p := hpar.mpr hqe
      by_cases hle : |mu| ≤ |lam|
      · have hqle : mu ^ q ≤ lam ^ q := by
          calc
            mu ^ q = |mu| ^ q := (hqe.pow_abs mu).symm
            _ ≤ |lam| ^ q := pow_le_pow_left₀ (abs_nonneg mu) hle q
            _ = lam ^ q := hqe.pow_abs lam
        have hple : mu ^ p ≤ lam ^ p := by
          calc
            mu ^ p = |mu| ^ p := (hpe.pow_abs mu).symm
            _ ≤ |lam| ^ p := pow_le_pow_left₀ (abs_nonneg mu) hle p
            _ = lam ^ p := hpe.pow_abs lam
        exact mul_nonneg (sub_nonneg.mpr hqle) (sub_nonneg.mpr hple)
      · have hle' : |lam| ≤ |mu| := le_of_not_ge hle
        have hqle : lam ^ q ≤ mu ^ q := by
          calc
            lam ^ q = |lam| ^ q := (hqe.pow_abs lam).symm
            _ ≤ |mu| ^ q := pow_le_pow_left₀ (abs_nonneg lam) hle' q
            _ = mu ^ q := hqe.pow_abs mu
        have hple : lam ^ p ≤ mu ^ p := by
          calc
            lam ^ p = |lam| ^ p := (hpe.pow_abs lam).symm
            _ ≤ |mu| ^ p := pow_le_pow_left₀ (abs_nonneg lam) hle' p
            _ = mu ^ p := hpe.pow_abs mu
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hqle) (sub_nonpos.mpr hple)
    · have hpe : Odd p := by
        refine Nat.not_even_iff_odd.mp ?_
        intro hpe
        exact (Nat.not_even_iff_odd.mpr hqo) (hpar.mp hpe)
      by_cases hle : mu ≤ lam
      · have hqle : mu ^ q ≤ lam ^ q := hqo.strictMono_pow.monotone hle
        have hple : mu ^ p ≤ lam ^ p := hpe.strictMono_pow.monotone hle
        exact mul_nonneg (sub_nonneg.mpr hqle) (sub_nonneg.mpr hple)
      · have hle' : lam ≤ mu := le_of_not_ge hle
        have hqle : lam ^ q ≤ mu ^ q := hqo.strictMono_pow.monotone hle'
        have hple : lam ^ p ≤ mu ^ p := hpe.strictMono_pow.monotone hle'
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hqle) (sub_nonpos.mpr hple)
  have hmain :
      lam ^ q * mu ^ p + lam ^ p * mu ^ q ≤ lam ^ q * lam ^ p + mu ^ q * mu ^ p := by
    nlinarith [hprod]
  calc
    lam ^ q * mu ^ p + lam ^ p * mu ^ q
        ≤ lam ^ q * lam ^ p + mu ^ q * mu ^ p := hmain
    _ = lam ^ (q + p) + mu ^ (q + p) := by
      rw [pow_add, pow_add]
    _ = lam ^ (2 * r) + mu ^ (2 * r) := by
      rw [hpq]

lemma hermitian_pow_eq {D : Type*} [Fintype D] [DecidableEq D] (A : Matrix D D ℝ)
    (hA : A.IsHermitian) (k : ℕ) :
    A ^ k =
      (hA.eigenvectorUnitary : Matrix D D ℝ) *
        diagonal (fun i => hA.eigenvalues i ^ k) *
        (hA.eigenvectorUnitary : Matrix D D ℝ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow ((Unitary.conjStarAlgAut ℝ (Matrix D D ℝ)) hA.eigenvectorUnitary)
    (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) k]
  simp [Unitary.conjStarAlgAut_apply, Matrix.diagonal_pow, Matrix.star_eq_conjTranspose,
    Matrix.mul_assoc]
  congr 1

lemma trace_conjTranspose_diagonal_mul_diagonal {D : Type*} [Fintype D] [DecidableEq D]
    (G : Matrix D D ℝ) (α β : D → ℝ) :
    Matrix.trace (Gᴴ * diagonal α * G * diagonal β)
      =
    ∑ i : D, ∑ j : D, α i * β j * (G i j) ^ 2 := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Finset.sum_mul, pow_two]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

lemma trace_basis_change {D : Type*} [Fintype D] [DecidableEq D] (H : Matrix D D ℝ)
    (hH : H.IsHermitian) (U V : Matrix D D ℝ)
    (α β : D → ℝ) :
    Matrix.trace (H * (U * diagonal α * Uᴴ) * H * (V * diagonal β * Vᴴ))
      =
    Matrix.trace (((Uᴴ * H * V)ᴴ) * diagonal α * (Uᴴ * H * V) * diagonal β) := by
  classical
  have hHt : Hᵀ = H := by
    simpa [Matrix.star_eq_conjTranspose] using hH.eq
  calc
    Matrix.trace (H * (U * diagonal α * Uᴴ) * H * (V * diagonal β * Vᴴ))
        = Matrix.trace ((H * (U * diagonal α * Uᴴ) * H * (V * diagonal β)) * Vᴴ) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace (Vᴴ * (H * (U * diagonal α * Uᴴ) * H * (V * diagonal β))) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (((Uᴴ * H * V)ᴴ) * diagonal α * (Uᴴ * H * V) * diagonal β) := by
          simp [Matrix.mul_assoc, hHt]

lemma trace_eigenbasis {D : Type*} [Fintype D] [DecidableEq D] (H W Y : Matrix D D ℝ)
    (hH : H.IsHermitian) (hW : W.IsHermitian) (hY : Y.IsHermitian)
    (a b : ℕ) :
    Matrix.trace (H * W ^ a * H * Y ^ b)
      =
    ∑ i : D, ∑ j : D,
      hW.eigenvalues i ^ a * hY.eigenvalues j ^ b *
        (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
          H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2 := by
  classical
  let U : Matrix D D ℝ := hW.eigenvectorUnitary
  let V : Matrix D D ℝ := hY.eigenvectorUnitary
  let G : Matrix D D ℝ := Uᴴ * H * V
  calc
    Matrix.trace (H * W ^ a * H * Y ^ b)
        = Matrix.trace
            (H * (U * diagonal (fun i => hW.eigenvalues i ^ a) * Uᴴ) *
              H * (V * diagonal (fun j => hY.eigenvalues j ^ b) * Vᴴ)) := by
          dsimp [U, V]
          conv_lhs =>
            rw [hermitian_pow_eq W hW a, hermitian_pow_eq Y hY b]
    _ = Matrix.trace (Gᴴ * diagonal (fun i => hW.eigenvalues i ^ a) *
          G * diagonal (fun j => hY.eigenvalues j ^ b)) := by
          simpa [G] using
            trace_basis_change H hH U V
              (fun i => hW.eigenvalues i ^ a) (fun j => hY.eigenvalues j ^ b)
    _ = ∑ i : D, ∑ j : D,
          hW.eigenvalues i ^ a * hY.eigenvalues j ^ b *
            (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
              H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2 := by
          simpa [G, U, V] using
            trace_conjTranspose_diagonal_mul_diagonal G
              (fun i => hW.eigenvalues i ^ a) (fun j => hY.eigenvalues j ^ b)

theorem tropp_fact_2_4 {D : Type*} [Fintype D] [DecidableEq D] (H W Y : Matrix D D ℝ)
    (hH : H.IsHermitian) (hW : W.IsHermitian) (hY : Y.IsHermitian)
    (r q : ℕ) (hq : q ≤ 2 * r) :
    Matrix.trace (H * W ^ q * H * Y ^ (2 * r - q))
        + Matrix.trace (H * W ^ (2 * r - q) * H * Y ^ q)
      ≤ Matrix.trace (H * H * (W ^ (2 * r) + Y ^ (2 * r))) := by
  classical
  let p := 2 * r - q
  let G : Matrix D D ℝ :=
    (hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
      H * (hY.eigenvectorUnitary : Matrix D D ℝ)
  have hRHS :
      Matrix.trace (H * H * (W ^ (2 * r) + Y ^ (2 * r)))
        =
      Matrix.trace (H * W ^ (2 * r) * H * Y ^ 0)
        + Matrix.trace (H * W ^ 0 * H * Y ^ (2 * r)) := by
    rw [Matrix.mul_add, Matrix.trace_add]
    simp [Matrix.mul_assoc]
    simpa [Matrix.mul_assoc] using (Matrix.trace_mul_cycle H (W ^ (2 * r)) H).symm
  rw [hRHS]
  rw [trace_eigenbasis H W Y hH hW hY q p,
    trace_eigenbasis H W Y hH hW hY p q,
    trace_eigenbasis H W Y hH hW hY (2 * r) 0,
    trace_eigenbasis H W Y hH hW hY 0 (2 * r)]
  dsimp [p, G]
  calc
    (∑ i : D, ∑ j : D,
          hW.eigenvalues i ^ q * hY.eigenvalues j ^ (2 * r - q) *
            (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
              H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2)
        +
        (∑ i : D, ∑ j : D,
          hW.eigenvalues i ^ (2 * r - q) * hY.eigenvalues j ^ q *
            (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
              H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2)
        =
        ∑ i : D, ∑ j : D,
          (hW.eigenvalues i ^ q * hY.eigenvalues j ^ (2 * r - q) *
              (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
                H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2
            +
            hW.eigenvalues i ^ (2 * r - q) * hY.eigenvalues j ^ q *
              (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
                H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2) := by
          simp [Finset.sum_add_distrib]
    _ ≤ ∑ i : D, ∑ j : D,
          (hW.eigenvalues i ^ (2 * r) * hY.eigenvalues j ^ 0 *
              (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
                H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2
            +
            hW.eigenvalues i ^ 0 * hY.eigenvalues j ^ (2 * r) *
              (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
                H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro j _hj
          have hs := scalar_bound (hW.eigenvalues i) (hY.eigenvalues j) r q hq
          have hsq :
              0 ≤
                (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
                  H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2 :=
            sq_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right hs hsq]
    _ =
        (∑ i : D, ∑ j : D,
          hW.eigenvalues i ^ (2 * r) * hY.eigenvalues j ^ 0 *
            (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
              H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2)
        +
        (∑ i : D, ∑ j : D,
          hW.eigenvalues i ^ 0 * hY.eigenvalues j ^ (2 * r) *
            (((hW.eigenvectorUnitary : Matrix D D ℝ)ᴴ *
              H * (hY.eigenvectorUnitary : Matrix D D ℝ)) i j) ^ 2) := by
          simp [Finset.sum_add_distrib]


-- ===== Iterate (D) =====


/-!

If `T : ℕ → ℝ` is a moment sequence with `T 0 = d`, nonneg, and the Tropp recursion
`T p ≤ (2p-1) · B · T (p-1)` (B ≥ 0), then `T p ≤ (2p-1)!! · B^p · d`,
where `(2p-1)!! = (2p)!/(2^p p!)`.

This is the "(D) iterate" arithmetic step of the general engine, independent of any
matrix machinery. Reusable.
-/

namespace TroppGeneral

/-- Double factorial of odd numbers `(2p-1)!! = (2p)!/(2^p · p!)`. -/
noncomputable def doubleFactOdd (p : ℕ) : ℝ :=
  (Nat.factorial (2 * p) : ℝ) / ((2 ^ p : ℝ) * (Nat.factorial p : ℝ))

@[simp] lemma doubleFactOdd_zero : doubleFactOdd 0 = 1 := by
  simp [doubleFactOdd]

/-- The recursion satisfied by `(2p-1)!!`: `(2(p+1)-1)!! = (2p+1) · (2p-1)!!`. -/
lemma doubleFactOdd_succ (p : ℕ) :
    doubleFactOdd (p + 1) = (2 * p + 1 : ℝ) * doubleFactOdd p := by
  unfold doubleFactOdd
  have hfac2 : (Nat.factorial (2 * (p + 1)) : ℝ)
      = (2 * (p + 1) : ℝ) * (2 * p + 1 : ℝ) * (Nat.factorial (2 * p) : ℝ) := by
    have h1 : 2 * (p + 1) = (2 * p + 1) + 1 := by ring
    rw [h1, Nat.factorial_succ]
    have h2 : (2 * p + 1) = (2 * p) + 1 := by ring
    rw [h2, Nat.factorial_succ]
    push_cast
    ring
  have hpow : (2 ^ (p + 1) : ℝ) = 2 * 2 ^ p := by rw [pow_succ]; ring
  have hfacp : (Nat.factorial (p + 1) : ℝ) = (p + 1 : ℝ) * (Nat.factorial p : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac2, hpow, hfacp]
  have hp1 : (0:ℝ) < (p + 1 : ℝ) := by positivity
  have hfp : (0:ℝ) < (Nat.factorial p : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hpw : (0:ℝ) < (2 ^ p : ℝ) := by positivity
  field_simp

lemma doubleFactOdd_nonneg (p : ℕ) : 0 ≤ doubleFactOdd p := by
  unfold doubleFactOdd; positivity

/-- **Iterate (eq 4.9).** Given the Tropp recursion `T p ≤ (2p-1) B T(p-1)`, conclude
`T p ≤ (2p-1)!! B^p · d`. -/
theorem recursion_iterate (T : ℕ → ℝ) (B d : ℝ) (hB : 0 ≤ B)
    (hT0 : T 0 = d) (hTnn : ∀ p, 0 ≤ T p)
    (hrec : ∀ p, 1 ≤ p → T p ≤ (2 * p - 1 : ℝ) * B * T (p - 1)) :
    ∀ p, T p ≤ doubleFactOdd p * B ^ p * d := by
  intro p
  induction p with
  | zero => simp [hT0]
  | succ k ih =>
    have hstep := hrec (k + 1) (by omega)
    -- T(k+1) ≤ (2(k+1)-1) B · T k = (2k+1) B · T k
    have hidx : (k + 1) - 1 = k := by omega
    rw [hidx] at hstep
    push_cast at hstep
    -- hstep : T (k+1) ≤ (2*↑k + 2 - 1) * B * T k  (normalize coefficient)
    have hstep' : T (k + 1) ≤ (2 * (k:ℝ) + 1) * B * T k := by
      have : (2 * ((k:ℝ) + 1) - 1) = (2 * (k:ℝ) + 1) := by ring
      calc T (k + 1) ≤ (2 * ((k:ℝ) + 1) - 1) * B * T k := by linarith [hstep]
        _ = (2 * (k:ℝ) + 1) * B * T k := by rw [this]
    have hstep := hstep'
    -- chain with IH
    have hcoefnn : (0:ℝ) ≤ (2 * k + 1 : ℝ) := by positivity
    calc T (k + 1) ≤ (2 * k + 1 : ℝ) * B * T k := hstep
      _ ≤ (2 * k + 1 : ℝ) * B * (doubleFactOdd k * B ^ k * d) := by
            apply mul_le_mul_of_nonneg_left ih
            exact mul_nonneg hcoefnn hB
      _ = doubleFactOdd (k + 1) * B ^ (k + 1) * d := by
            rw [doubleFactOdd_succ]; ring


end TroppGeneral

-- ===== SBP (C) + foundation =====


/-!

GENERAL `{Hᵢ}` engine, continuation of Draft_tropp_general / Draft_vanhandel_general.

We work over the sign cube `Finset ι` with uniform weight.  `Xmat H eps = ∑_c sgn(eps,c)•H_c`.
This file builds:
 (C) summation-by-parts (4.5): the conditioning/flip identity, and
 (4.7) the resulting q-sum,
leading to the per-step recursion (4.8):
   Ex tr X^{2p} ≤ (2p-1)·normV·Ex tr X^{2p-2}.
which feeds `recursion_iterate` (D, done) to give (4.9).
-/

namespace TroppSBP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rademacher sign from a +1-subset encoding. -/
def sgn (eps : Finset ι) (c : ι) : ℝ := if c ∈ eps then 1 else -1

omit [Fintype ι] in
@[simp] lemma sgn_sq (eps : Finset ι) (c : ι) : sgn eps c ^ 2 = 1 := by
  unfold sgn; split <;> norm_num

omit [Fintype ι] in
@[simp] lemma sgn_mul_self (eps : Finset ι) (c : ι) : sgn eps c * sgn eps c = 1 := by
  unfold sgn; split <;> norm_num

noncomputable def Ex (F : Finset ι → ℝ) : ℝ :=
  ∑ eps : Finset ι, ((1:ℝ)/2) ^ Fintype.card ι * F eps

omit [DecidableEq ι] in
lemma Ex_const_mul (c : ℝ) (F : Finset ι → ℝ) :
    Ex (fun eps => c * F eps) = c * Ex F := by
  unfold Ex; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro eps _; ring

omit [DecidableEq ι] in
lemma Ex_add (F G : Finset ι → ℝ) :
    Ex (fun eps => F eps + G eps) = Ex F + Ex G := by
  unfold Ex; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro eps _; ring

omit [DecidableEq ι] in
lemma Ex_sub (F G : Finset ι → ℝ) :
    Ex (fun eps => F eps - G eps) = Ex F - Ex G := by
  unfold Ex; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro eps _; ring

omit [DecidableEq ι] in
lemma Ex_sum {κ : Type*} (s : Finset κ) (F : κ → Finset ι → ℝ) :
    Ex (fun eps => ∑ k ∈ s, F k eps) = ∑ k ∈ s, Ex (F k) := by
  unfold Ex
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro eps _
  rw [Finset.mul_sum]

omit [DecidableEq ι] in
lemma Ex_mono (F G : Finset ι → ℝ) (h : ∀ eps, F eps ≤ G eps) : Ex F ≤ Ex G := by
  unfold Ex; apply Finset.sum_le_sum; intro eps _
  apply mul_le_mul_of_nonneg_left (h eps); positivity

lemma Ex_congr {F G : Finset ι → ℝ} (h : ∀ eps, F eps = G eps) : Ex F = Ex G := by
  unfold Ex; apply Finset.sum_congr rfl; intro eps _; rw [h eps]

/-- `X_ε = ∑_c sgn(ε,c)•H_c`. -/
noncomputable def Xmat {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ) (eps : Finset ι) :
    Matrix D D ℝ := ∑ c : ι, (sgn eps c) • H c

/-- The "rest" series excluding coordinate `c`: `R_c(ε) = ∑_{c'≠c} sgn(ε,c')•H_{c'}`. -/
noncomputable def Rest {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ) (c : ι) (eps : Finset ι) :
    Matrix D D ℝ := ∑ c' ∈ (Finset.univ.erase c), (sgn eps c') • H c'

/-- `X_ε = R_c(ε) + sgn(ε,c)•H_c`. -/
lemma Xmat_split {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ) (c : ι) (eps : Finset ι) :
    Xmat H eps = Rest H c eps + (sgn eps c) • H c := by
  unfold Xmat Rest
  rw [add_comm]
  exact (Finset.add_sum_erase Finset.univ (fun c' => (sgn eps c') • H c') (Finset.mem_univ c)).symm

/-- Flipping membership of `c` does not change `Rest H c` (it omits `c`). -/
lemma Rest_flip_invariant {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ) (c : ι) (eps : Finset ι) :
    Rest H c (symmDiff eps {c}) = Rest H c eps := by
  unfold Rest
  apply Finset.sum_congr rfl
  intro c' hc'
  have hne : c' ≠ c := Finset.ne_of_mem_erase hc'
  have : sgn (symmDiff eps {c}) c' = sgn eps c' := by
    unfold sgn
    have hiff : (c' ∈ symmDiff eps ({c} : Finset ι)) ↔ (c' ∈ eps) := by
      simp [Finset.mem_symmDiff, hne]
    by_cases h : c' ∈ eps
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
  rw [this]

omit [Fintype ι] in
lemma sgn_flip (c : ι) (eps : Finset ι) :
    sgn (symmDiff eps {c}) c = - sgn eps c := by
  unfold sgn
  by_cases h : c ∈ eps
  · have hnot : c ∉ symmDiff eps ({c} : Finset ι) := by simp [Finset.mem_symmDiff, h]
    simp [h, hnot]
  · have hin : c ∈ symmDiff eps ({c} : Finset ι) := by simp [Finset.mem_symmDiff, h]
    simp [h, hin]

/-- The flip `eps ↦ eps Δ {c}` is a measure-preserving involution on the sign cube, so
`Ex F = ½·Ex(F + F∘flip)`. This is the symmetrization step underlying summation by parts. -/
lemma Ex_symmetrize (c : ι) (F : Finset ι → ℝ) :
    Ex F = Ex (fun eps => (1/2 : ℝ) * (F eps + F (symmDiff eps {c}))) := by
  classical
  have hbij : Ex (fun eps => F (symmDiff eps {c})) = Ex F := by
    unfold Ex
    apply Finset.sum_nbij' (fun eps => symmDiff eps {c}) (fun eps => symmDiff eps {c})
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact symmDiff_symmDiff_cancel_right {c} a
    · intro a _; exact symmDiff_symmDiff_cancel_right {c} a
    · intro a _; rfl
  calc Ex F = (1/2 : ℝ) * (Ex F + Ex (fun eps => F (symmDiff eps {c}))) := by
            rw [hbij]; ring
    _ = (1/2 : ℝ) * Ex (fun eps => F eps + F (symmDiff eps {c})) := by rw [Ex_add]
    _ = Ex (fun eps => (1/2 : ℝ) * (F eps + F (symmDiff eps {c}))) := by rw [Ex_const_mul]

/-! ## Trace linearity in the leading factor -/

/-- `tr(X · X^{2p-1}) = ∑_c sgn(c) · tr(H_c · X^{2p-1})` (linearity of `X = ∑_c sgn·H_c`). -/
lemma trace_lead_split {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ) (eps : Finset ι) (m : ℕ) :
    Matrix.trace (Xmat H eps * (Xmat H eps) ^ m)
      = ∑ c : ι, sgn eps c * Matrix.trace (H c * (Xmat H eps) ^ m) := by
  conv_lhs => rw [show Xmat H eps * (Xmat H eps) ^ m
      = (∑ c : ι, (sgn eps c) • H c) * (Xmat H eps) ^ m from by rw [Xmat]]
  rw [Finset.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-! ## The per-coordinate summation-by-parts identity (Tropp 4.5 + 4.7).

For fixed `c`, write `s = sgn(ε,c)`, `R = Rest_c(ε)`, `W = X(ε) = R + s•H_c`,
`Y = X(ε Δ {c}) = R − s•H_c`.  Then `W − Y = 2s•H_c`, and via telescoping (eq 4.6)
plus the flip-involution symmetrization (eq 4.5):

  Ex[ sgn(c)·tr(H_c X^{n}) ]
    = Ex[ ∑_{q<n} tr(H_c · X(ε)^q · H_c · X(ε Δ {c})^{n-1-q}) ]      (for `n = 2p-1`).

`Y` appears as the flipped iterate `Xmat H (ε Δ {c})`. -/

/-- `Xmat H (ε Δ {c}) = Rest H c ε − sgn(ε,c)•H_c` (the flipped iterate; companion to
`Xmat_split`). -/
lemma Xmat_flip_split {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ) (c : ι) (eps : Finset ι) :
    Xmat H (symmDiff eps {c}) = Rest H c eps - (sgn eps c) • H c := by
  rw [Xmat_split H c (symmDiff eps {c}), Rest_flip_invariant, sgn_flip]
  rw [neg_smul, ← sub_eq_add_neg]

/-- `W − Y = 2·sgn(c)•H_c` where `W = X(ε)`, `Y = X(ε Δ {c})`. -/
lemma Xmat_diff {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ) (c : ι) (eps : Finset ι) :
    Xmat H eps - Xmat H (symmDiff eps {c}) = (2 * sgn eps c) • H c := by
  rw [Xmat_split H c eps, Xmat_flip_split H c eps]
  rw [add_sub_sub_cancel, ← two_smul ℝ ((sgn eps c) • H c), smul_smul]

/-- **Per-coordinate summation-by-parts identity (Tropp eq 4.5 + 4.7).**
For fixed coordinate `c` and `n = 2p−1` (any `n` works), the symmetrized leading-factor
term equals the telescoped double-`H_c` `q`-sum, with the flipped iterate `Y = X(ε Δ {c})`. -/
lemma sbp_coord {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ) (c : ι) (n : ℕ) :
    Ex (fun eps => sgn eps c * Matrix.trace (H c * (Xmat H eps) ^ n))
      = Ex (fun eps => ∑ q ∈ Finset.range n,
          Matrix.trace (H c * (Xmat H eps) ^ q * H c
            * (Xmat H (symmDiff eps {c})) ^ (n - 1 - q))) := by
  classical
  rw [Ex_symmetrize c (fun eps => sgn eps c * Matrix.trace (H c * (Xmat H eps) ^ n))]
  apply Finset.sum_congr rfl
  intro eps _
  congr 1
  simp only []
  -- pointwise: ½(g eps + g (flip eps)) = ∑_q tr(H_c W^q H_c Y^{n-1-q})
  set s : ℝ := sgn eps c with hs
  set W : Matrix D D ℝ := Xmat H eps with hW
  set Y : Matrix D D ℝ := Xmat H (symmDiff eps {c}) with hY
  have hsgnflip : sgn (symmDiff eps {c}) c = - s := sgn_flip c eps
  -- g (flip eps) = -s · tr(H_c Y^n)
  have hg2 : sgn (symmDiff eps {c}) c
        * Matrix.trace (H c * (Xmat H (symmDiff eps {c})) ^ n)
      = - s * Matrix.trace (H c * Y ^ n) := by
    rw [hsgnflip]
  -- ½(s·tr(H_c W^n) + (-s)·tr(H_c Y^n)) = ½·s·tr(H_c (W^n - Y^n))
  have hWmY : W - Y = (2 * s) • H c := by
    rw [hW, hY]; exact Xmat_diff H c eps
  have htel : W ^ n - Y ^ n
      = ∑ q ∈ Finset.range n, W ^ q * (W - Y) * Y ^ (n - 1 - q) := by
    -- use the proven telescope from the general draft, inlined here:
    clear hg2 hsgnflip
    induction n with
    | zero => simp
    | succ k ih =>
      have hrec : W ^ (k + 1) - Y ^ (k + 1)
          = (W ^ k - Y ^ k) * Y + W ^ k * (W - Y) := by
        rw [pow_succ, pow_succ]; noncomm_ring
      rw [hrec, ih, Finset.sum_mul, Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mem_range] at hq
        have hidx : k - 1 - q + 1 = k + 1 - 1 - q := by omega
        rw [mul_assoc, mul_assoc, ← pow_succ, hidx, ← mul_assoc]
      · have hidx : k + 1 - 1 - k = 0 := by omega
        rw [hidx, pow_zero, mul_one]
  -- assemble
  have hs2 : s * s = 1 := by rw [hs]; exact sgn_mul_self eps c
  have key : (1:ℝ)/2 * (s * Matrix.trace (H c * W ^ n) + -s * Matrix.trace (H c * Y ^ n))
      = ∑ q ∈ Finset.range n,
          Matrix.trace (H c * W ^ q * H c * Y ^ (n - 1 - q)) := by
    have hcombine : s * Matrix.trace (H c * W ^ n) + -s * Matrix.trace (H c * Y ^ n)
        = s * Matrix.trace (H c * (W ^ n - Y ^ n)) := by
      rw [Matrix.mul_sub, Matrix.trace_sub]; ring
    rw [hcombine, htel]
    rw [Matrix.mul_sum, Matrix.trace_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    -- term: ½ · s · tr(H_c · (W^q · (W-Y) · Y^{n-1-q})) with W-Y = (2s)•H_c
    rw [hWmY]
    -- (2s)•H_c slots in: tr(H_c·W^q·((2s)•H_c)·Y^{n-1-q}) = (2s)·tr(H_c W^q H_c Y^{n-1-q})
    have hpull : Matrix.trace (H c * (W ^ q * (2 * s) • H c * Y ^ (n - 1 - q)))
        = (2 * s) * Matrix.trace (H c * W ^ q * H c * Y ^ (n - 1 - q)) := by
      have e1 : H c * (W ^ q * (2 * s) • H c * Y ^ (n - 1 - q))
          = (2 * s) • (H c * W ^ q * H c * Y ^ (n - 1 - q)) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul]
        congr 1
        noncomm_ring
      rw [e1, Matrix.trace_smul, smul_eq_mul]
    rw [hpull]
    rw [show (1:ℝ)/2 * (s * ((2 * s) * Matrix.trace (H c * W ^ q * H c * Y ^ (n - 1 - q))))
        = (s * s) * Matrix.trace (H c * W ^ q * H c * Y ^ (n - 1 - q)) from by ring]
    rw [hs2, one_mul]
  -- goal after `congr 1`: ½(g + g∘flip) = ∑..., reduces to `key` after rewriting hg2
  rw [hg2]
  exact key

/-! ## (4.8) assembly: per-step recursion -/

/-- `V = ∑_c H_c²`, the variance proxy (`∑ Hᵢ²` in Tropp 4.8). -/
noncomputable def VarProxy {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ) :
    Matrix D D ℝ := ∑ c : ι, H c * H c

/-- **Pairing-sum form of Fact 2.4.** Summing `tr(H Wᵍ H Y^{2r-q})` over `q = 0..2r`,
pair `q ↔ 2r-q` and apply `tropp_fact_2_4`:
`∑_{q=0}^{2r} tr(H Wᵍ H Y^{2r-q}) ≤ ((2r+1)/2)·tr(H²(W^{2r}+Y^{2r}))`. -/
lemma qsum_le {D : Type*} [Fintype D] [DecidableEq D] (H W Y : Matrix D D ℝ)
    (hH : H.IsHermitian) (hW : W.IsHermitian) (hY : Y.IsHermitian) (r : ℕ) :
    ∑ q ∈ Finset.range (2 * r + 1),
        Matrix.trace (H * W ^ q * H * Y ^ (2 * r - q))
      ≤ ((2 * r + 1 : ℝ) / 2) * Matrix.trace (H * H * (W ^ (2 * r) + Y ^ (2 * r))) := by
  classical
  set L := ∑ q ∈ Finset.range (2 * r + 1),
      Matrix.trace (H * W ^ q * H * Y ^ (2 * r - q)) with hL
  -- reflected copy: ∑_q tr(H W^{2r-q} H Y^q) = L (reindex q ↦ 2r-q)
  have hrefl : ∑ q ∈ Finset.range (2 * r + 1),
        Matrix.trace (H * W ^ (2 * r - q) * H * Y ^ q) = L := by
    rw [hL]
    rw [← Finset.sum_range_reflect
        (fun q => Matrix.trace (H * W ^ (2 * r - q) * H * Y ^ q)) (2 * r + 1)]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_range] at hq
    have h1 : 2 * r + 1 - 1 - q = 2 * r - q := by omega
    have h2 : 2 * r - (2 * r - q) = q := by omega
    rw [h1, h2]
  -- 2L = ∑_q (tr(H W^q H Y^{2r-q}) + tr(H W^{2r-q} H Y^q)) ≤ (2r+1)·tr(H²(W^{2r}+Y^{2r}))
  have htwoL : 2 * L = ∑ q ∈ Finset.range (2 * r + 1),
      (Matrix.trace (H * W ^ q * H * Y ^ (2 * r - q))
        + Matrix.trace (H * W ^ (2 * r - q) * H * Y ^ q)) := by
    rw [Finset.sum_add_distrib, hrefl, two_mul]
  have hbound : ∑ q ∈ Finset.range (2 * r + 1),
      (Matrix.trace (H * W ^ q * H * Y ^ (2 * r - q))
        + Matrix.trace (H * W ^ (2 * r - q) * H * Y ^ q))
      ≤ ∑ q ∈ Finset.range (2 * r + 1),
          Matrix.trace (H * H * (W ^ (2 * r) + Y ^ (2 * r))) := by
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.mem_range] at hq
    exact tropp_fact_2_4 H W Y hH hW hY r q (by omega)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hbound
  -- 2L ≤ (2r+1)·RHS ⇒ L ≤ ((2r+1)/2)·RHS
  have : (2 : ℝ) * L ≤ (2 * r + 1 : ℝ) * Matrix.trace (H * H * (W ^ (2 * r) + Y ^ (2 * r))) := by
    calc (2:ℝ) * L = ∑ q ∈ Finset.range (2 * r + 1),
            (Matrix.trace (H * W ^ q * H * Y ^ (2 * r - q))
              + Matrix.trace (H * W ^ (2 * r - q) * H * Y ^ q)) := htwoL
      _ ≤ ((2 * r + 1 : ℕ) : ℝ) * Matrix.trace (H * H * (W ^ (2 * r) + Y ^ (2 * r))) := hbound
      _ = (2 * r + 1 : ℝ) * Matrix.trace (H * H * (W ^ (2 * r) + Y ^ (2 * r))) := by push_cast; ring
  linarith

/-- `Xmat` is Hermitian (symmetric) when each `H_c` is. -/
lemma Xmat_isHermitian {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ)
    (hHerm : ∀ c, (H c).IsHermitian) (eps : Finset ι) : (Xmat H eps).IsHermitian := by
  unfold Xmat Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Matrix.conjTranspose_smul, star_trivial, (hHerm c)]

/-- Flip-invariance: `Ex(fun eps => F (eps Δ {c})) = Ex F`. -/
lemma Ex_flip (c : ι) (F : Finset ι → ℝ) :
    Ex (fun eps => F (symmDiff eps {c})) = Ex F := by
  classical
  unfold Ex
  apply Finset.sum_nbij' (fun eps => symmDiff eps {c}) (fun eps => symmDiff eps {c})
  · intro a _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_univ _
  · intro a _; exact symmDiff_symmDiff_cancel_right {c} a
  · intro a _; exact symmDiff_symmDiff_cancel_right {c} a
  · intro a _; rfl

/-- **Per-coordinate (4.7)→(4.8) trace bound.** For fixed `c` and `r`, with `n = 2r+1`:
`Ex[ sgn(c)·tr(H_c·X^{2r+1}) ] ≤ (2r+1)·Ex[ tr(H_c²·X^{2r}) ]`. -/
lemma coord_recursion {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ)
    (hHerm : ∀ c, (H c).IsHermitian) (c : ι) (r : ℕ) :
    Ex (fun eps => sgn eps c * Matrix.trace (H c * (Xmat H eps) ^ (2 * r + 1)))
      ≤ (2 * r + 1 : ℝ) * Ex (fun eps => Matrix.trace (H c * H c * (Xmat H eps) ^ (2 * r))) := by
  classical
  -- (4.7): rewrite via sbp_coord (n = 2r+1, so n-1 = 2r)
  rw [sbp_coord H c (2 * r + 1)]
  -- pointwise: the q-sum ≤ ((2r+1)/2)·tr(H_c²(X^{2r} + Y^{2r}))   [qsum_le, n-1-q = 2r-q]
  have hstep : ∀ eps : Finset ι,
      (∑ q ∈ Finset.range (2 * r + 1),
        Matrix.trace (H c * (Xmat H eps) ^ q * H c
          * (Xmat H (symmDiff eps {c})) ^ (2 * r + 1 - 1 - q)))
      ≤ ((2 * r + 1 : ℝ) / 2)
          * Matrix.trace (H c * H c
              * ((Xmat H eps) ^ (2 * r) + (Xmat H (symmDiff eps {c})) ^ (2 * r))) := by
    intro eps
    have hidx : ∀ q, 2 * r + 1 - 1 - q = 2 * r - q := by intro q; omega
    simp only [hidx]
    exact qsum_le (H c) (Xmat H eps) (Xmat H (symmDiff eps {c}))
      (hHerm c) (Xmat_isHermitian H hHerm eps)
      (Xmat_isHermitian H hHerm (symmDiff eps {c})) r
  -- average the pointwise bound
  refine le_trans (Ex_mono _ _ hstep) ?_
  -- RHS: ((2r+1)/2)·Ex[tr(H_c²(X^{2r}+Y^{2r}))] = (2r+1)·Ex[tr(H_c² X^{2r})]  via Ex_flip
  have hsplit : ∀ eps : Finset ι,
      ((2 * r + 1 : ℝ) / 2)
        * Matrix.trace (H c * H c
            * ((Xmat H eps) ^ (2 * r) + (Xmat H (symmDiff eps {c})) ^ (2 * r)))
      = ((2 * r + 1 : ℝ) / 2)
          * (Matrix.trace (H c * H c * (Xmat H eps) ^ (2 * r))
            + Matrix.trace (H c * H c * (Xmat H (symmDiff eps {c})) ^ (2 * r))) := by
    intro eps; rw [Matrix.mul_add, Matrix.trace_add]
  rw [show (fun eps : Finset ι => ((2 * r + 1 : ℝ) / 2)
        * Matrix.trace (H c * H c
            * ((Xmat H eps) ^ (2 * r) + (Xmat H (symmDiff eps {c})) ^ (2 * r))))
      = (fun eps => ((2 * r + 1 : ℝ) / 2)
          * (Matrix.trace (H c * H c * (Xmat H eps) ^ (2 * r))
            + Matrix.trace (H c * H c * (Xmat H (symmDiff eps {c})) ^ (2 * r))))
        from funext hsplit]
  rw [Ex_const_mul]
  rw [Ex_add]
  rw [Ex_flip c (fun eps => Matrix.trace (H c * H c * (Xmat H eps) ^ (2 * r)))]
  set A := Ex (fun eps => Matrix.trace (H c * H c * (Xmat H eps) ^ (2 * r))) with hA
  apply le_of_eq; ring

/-- Even power of a Hermitian real matrix is PSD: `M^{2r}` is PSD. -/
lemma even_pow_posSemidef {D : Type*} [Fintype D] [DecidableEq D] {M : Matrix D D ℝ}
    (hM : M.IsHermitian) (r : ℕ) : (M ^ (2 * r)).PosSemidef := by
  have hHpow : (M ^ r)ᴴ = M ^ r := (Matrix.IsHermitian.pow hM r)
  have hsplit : M ^ (2 * r) = (M ^ r)ᴴ * (M ^ r) := by
    rw [hHpow, two_mul, pow_add]
  rw [hsplit]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **Per-step recursion (Tropp eq 4.8).** With `V = ∑_c H_c²` and `normV` a bound on
the eigenvalues of `V`:
`Ex[ tr X^{2(r+1)} ] ≤ (2r+1)·normV·Ex[ tr X^{2r} ]`. -/
lemma step_recursion {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ)
    (hHerm : ∀ c, (H c).IsHermitian) (r : ℕ) (normV : ℝ)
    (hVHerm : (VarProxy H).IsHermitian)
    (hnormV : ∀ i, hVHerm.eigenvalues i ≤ normV) :
    Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * (r + 1))))
      ≤ (2 * r + 1 : ℝ) * normV * Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * r))) := by
  classical
  -- Step 1+2: split leading factor
  have h12 : Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * (r + 1))))
      = ∑ c : ι, Ex (fun eps => sgn eps c * Matrix.trace (H c * (Xmat H eps) ^ (2 * r + 1))) := by
    have hpow : ∀ eps : Finset ι, (Xmat H eps) ^ (2 * (r + 1))
        = Xmat H eps * (Xmat H eps) ^ (2 * r + 1) := by
      intro eps
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 from by omega, pow_succ']
    rw [show (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * (r + 1))))
          = (fun eps => Matrix.trace (Xmat H eps * (Xmat H eps) ^ (2 * r + 1)))
        from funext (fun eps => by rw [hpow eps])]
    rw [show (fun eps => Matrix.trace (Xmat H eps * (Xmat H eps) ^ (2 * r + 1)))
          = (fun eps => ∑ c : ι, sgn eps c * Matrix.trace (H c * (Xmat H eps) ^ (2 * r + 1)))
        from funext (fun eps => trace_lead_split H eps (2 * r + 1))]
    rw [Ex_sum]
  rw [h12]
  -- Step 3: coord_recursion termwise
  have h3 : ∑ c : ι, Ex (fun eps => sgn eps c * Matrix.trace (H c * (Xmat H eps) ^ (2 * r + 1)))
      ≤ ∑ c : ι, (2 * r + 1 : ℝ) * Ex (fun eps => Matrix.trace (H c * H c * (Xmat H eps) ^ (2 * r))) := by
    apply Finset.sum_le_sum
    intro c _
    exact coord_recursion H hHerm c r
  refine le_trans h3 ?_
  -- Step 4: pull (2r+1) out and collapse ∑_c tr(H_c² M) = tr(V M)
  rw [← Finset.mul_sum]
  rw [show ∑ c : ι, Ex (fun eps => Matrix.trace (H c * H c * (Xmat H eps) ^ (2 * r)))
        = Ex (fun eps => Matrix.trace ((VarProxy H) * (Xmat H eps) ^ (2 * r))) from by
        rw [← Ex_sum]
        apply congrArg
        funext eps
        unfold VarProxy
        rw [Finset.sum_mul, Matrix.trace_sum]]
  -- Step 5: Fact 2.2 pointwise: tr(V·M) ≤ normV·tr M, M = X^{2r} PSD
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- Ex monotone of pointwise Fact 2.2
  have h5 : ∀ eps : Finset ι,
      Matrix.trace ((VarProxy H) * (Xmat H eps) ^ (2 * r))
        ≤ normV * Matrix.trace ((Xmat H eps) ^ (2 * r)) := by
    intro eps
    exact tropp_fact_2_2 (VarProxy H) ((Xmat H eps) ^ (2 * r)) hVHerm
      (even_pow_posSemidef (Xmat_isHermitian H hHerm eps) r) normV hnormV
  refine le_trans (Ex_mono _ _ h5) ?_
  rw [Ex_const_mul]

omit [DecidableEq ι] in
lemma Ex_nonneg (F : Finset ι → ℝ) (hF : ∀ eps, 0 ≤ F eps) : 0 ≤ Ex F := by
  unfold Ex; apply Finset.sum_nonneg; intro eps _
  apply mul_nonneg _ (hF eps); positivity

omit [DecidableEq ι] in
lemma Ex_const (a : ℝ) : Ex (fun _ : Finset ι => a) = a := by
  unfold Ex
  rw [← Finset.sum_mul]
  have hcard : (Finset.univ : Finset (Finset ι)).card = 2 ^ Fintype.card ι := by
    rw [Finset.card_univ]; exact Fintype.card_finset
  rw [Finset.sum_const, hcard, nsmul_eq_mul, div_pow, one_pow]
  push_cast; field_simp

/-- `Ex[ tr X^{2p} ] ≥ 0` (each `X^{2p}` is PSD, trace nonneg). -/
lemma Ex_trace_even_nonneg {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ)
    (hHerm : ∀ c, (H c).IsHermitian) (p : ℕ) :
    0 ≤ Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * p))) := by
  apply Ex_nonneg
  intro eps
  exact (even_pow_posSemidef (Xmat_isHermitian H hHerm eps) p).trace_nonneg

/-- **GENERAL TROPP RADEMACHER MATRIX `2p`-TRACE MOMENT (eq 4.9).**
For any finite family `{H_c}` of Hermitian `d×d` real matrices, Rademacher signs over the
sign cube `Finset ι`, `X_ε = ∑_c sgn(ε,c)·H_c`, `V = ∑_c H_c²` with `normV` bounding the
eigenvalues of `V`:
`Ex[ tr X^{2p} ] ≤ (2p-1)!! · normV^p · d`. -/
theorem general_2p_trace_moment {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ)
    (hHerm : ∀ c, (H c).IsHermitian) (normV : ℝ) (hnormVnn : 0 ≤ normV)
    (hVHerm : (VarProxy H).IsHermitian)
    (hnormV : ∀ i, hVHerm.eigenvalues i ≤ normV) (p : ℕ) :
    Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * p)))
      ≤ TroppGeneral.doubleFactOdd p * normV ^ p * (Fintype.card D : ℝ) := by
  classical
  set T : ℕ → ℝ := fun k => Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * k))) with hT
  have hT0 : T 0 = (Fintype.card D : ℝ) := by
    rw [hT]; simp only [Nat.mul_zero, pow_zero]
    rw [show (fun _ : Finset ι => Matrix.trace (1 : Matrix D D ℝ))
          = (fun _ : Finset ι => (Fintype.card D : ℝ)) from funext (fun _ => by
            rw [Matrix.trace_one])]
    exact Ex_const (Fintype.card D : ℝ)
  have hTnn : ∀ k, 0 ≤ T k := fun k => Ex_trace_even_nonneg H hHerm k
  have hrec : ∀ k, 1 ≤ k → T k ≤ (2 * k - 1 : ℝ) * normV * T (k - 1) := by
    intro k hk
    obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
    have := step_recursion H hHerm r normV hVHerm hnormV
    have hidx : (r + 1) - 1 = r := by omega
    rw [hT]; rw [hidx]
    calc Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * (r + 1))))
        ≤ (2 * r + 1 : ℝ) * normV * Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * r))) := this
      _ = (2 * (r + 1 : ℕ) - 1 : ℝ) * normV * Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * r))) := by
            push_cast; ring
  exact TroppGeneral.recursion_iterate T normV (Fintype.card D : ℝ) hnormVnn hT0 hTnn hrec p

#print axioms general_2p_trace_moment

/-- **Trace-kept step (van Handel first step).** `Ex tr X^{2(r+1)} ≤ (2r+1)·Ex tr(V·X^{2r})`.
Elementary; reuses `coord_recursion`. The V is KEPT inside the trace (no Fact-2.2 collapse). -/
lemma trace_kept_step {D : Type*} [Fintype D] [DecidableEq D] (H : ι → Matrix D D ℝ)
    (hHerm : ∀ c, (H c).IsHermitian) (r : ℕ) :
    Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * (r + 1))))
      ≤ (2 * r + 1 : ℝ) *
          Ex (fun eps => Matrix.trace ((VarProxy H) * (Xmat H eps) ^ (2 * r))) := by
  classical
  have h12 : Ex (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * (r + 1))))
      = ∑ c : ι, Ex (fun eps => sgn eps c * Matrix.trace (H c * (Xmat H eps) ^ (2 * r + 1))) := by
    have hpow : ∀ eps : Finset ι, (Xmat H eps) ^ (2 * (r + 1))
        = Xmat H eps * (Xmat H eps) ^ (2 * r + 1) := by
      intro eps
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 from by omega, pow_succ']
    rw [show (fun eps => Matrix.trace ((Xmat H eps) ^ (2 * (r + 1))))
          = (fun eps => Matrix.trace (Xmat H eps * (Xmat H eps) ^ (2 * r + 1)))
        from funext (fun eps => by rw [hpow eps])]
    rw [show (fun eps => Matrix.trace (Xmat H eps * (Xmat H eps) ^ (2 * r + 1)))
          = (fun eps => ∑ c : ι, sgn eps c * Matrix.trace (H c * (Xmat H eps) ^ (2 * r + 1)))
        from funext (fun eps => trace_lead_split H eps (2 * r + 1))]
    rw [Ex_sum]
  rw [h12]
  have h3 : ∑ c : ι, Ex (fun eps => sgn eps c * Matrix.trace (H c * (Xmat H eps) ^ (2 * r + 1)))
      ≤ ∑ c : ι, (2 * r + 1 : ℝ) * Ex (fun eps => Matrix.trace (H c * H c * (Xmat H eps) ^ (2 * r))) := by
    apply Finset.sum_le_sum
    intro c _
    exact coord_recursion H hHerm c r
  refine le_trans h3 ?_
  rw [← Finset.mul_sum]
  apply le_of_eq
  congr 1
  rw [← Ex_sum]
  apply congrArg
  funext eps
  unfold VarProxy
  rw [Finset.sum_mul, Matrix.trace_sum]

#print axioms trace_kept_step

end TroppSBP

-- ===== Dilation brick =====

open Matrix
open scoped BigOperators

/-!
Hermitian dilation trace identity (foundational brick for the matrix-Khintchine
application to fixed-matrix centered sampling, CR2008 §6.1 Thm 6.3).

For a rectangular `S : Matrix (Fin n1) (Fin n2) ℝ`, the Hermitian dilation
`ℋ = fromBlocks 0 S Sᵀ 0` (size `n1 ⊕ n2`) satisfies
`trace (ℋ^(2n)) = trace ((S Sᵀ)^n) + trace ((Sᵀ S)^n)`.
This lets the symmetric trace-moment engine (Tropp / b6bf4feb) on the Hermitian `ℋ`
control the rectangular moment `trace ((S Sᵀ)^n)`.
-/

namespace DilationBrick

variable {n1 n2 : ℕ}

/-- Trace of a block matrix = trace of top-left + trace of bottom-right block. -/
lemma trace_fromBlocks {R : Type*} [AddCommMonoid R]
    (A : Matrix (Fin n1) (Fin n1) R) (B : Matrix (Fin n1) (Fin n2) R)
    (C : Matrix (Fin n2) (Fin n1) R) (D : Matrix (Fin n2) (Fin n2) R) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Fintype.sum_sum_type]
  simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

/-- The dilation matrix `ℋ = [[0, S], [Sᵀ, 0]]`. -/
noncomputable def dilation (S : Matrix (Fin n1) (Fin n2) ℝ) :
    Matrix (Fin n1 ⊕ Fin n2) (Fin n1 ⊕ Fin n2) ℝ :=
  Matrix.fromBlocks 0 S Sᵀ 0

/-- `ℋ² = [[S Sᵀ, 0], [0, Sᵀ S]]`. -/
lemma dilation_sq (S : Matrix (Fin n1) (Fin n2) ℝ) :
    (dilation S) ^ 2 = Matrix.fromBlocks (S * Sᵀ) 0 0 (Sᵀ * S) := by
  rw [pow_two, dilation, Matrix.fromBlocks_multiply]
  simp

/-- `ℋ^(2n) = [[(S Sᵀ)^n, 0], [0, (Sᵀ S)^n]]`. -/
lemma dilation_even_pow (S : Matrix (Fin n1) (Fin n2) ℝ) (n : ℕ) :
    (dilation S) ^ (2 * n)
      = Matrix.fromBlocks ((S * Sᵀ) ^ n) 0 0 ((Sᵀ * S) ^ n) := by
  induction n with
  | zero => simp [Matrix.fromBlocks_one]
  | succ k ih =>
    have : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [this, pow_add, ih, dilation_sq, Matrix.fromBlocks_multiply]
    simp [pow_succ]

/-- **Dilation trace identity.** `trace (ℋ^(2n)) = trace ((S Sᵀ)^n) + trace ((Sᵀ S)^n)`. -/
lemma trace_dilation_even_pow (S : Matrix (Fin n1) (Fin n2) ℝ) (n : ℕ) :
    Matrix.trace ((dilation S) ^ (2 * n))
      = Matrix.trace ((S * Sᵀ) ^ n) + Matrix.trace ((Sᵀ * S) ^ n) := by
  rw [dilation_even_pow, trace_fromBlocks]

/-- The dilation is Hermitian (symmetric, real). -/
lemma dilation_isHermitian (S : Matrix (Fin n1) (Fin n2) ℝ) :
    (dilation S).IsHermitian := by
  unfold dilation Matrix.IsHermitian
  rw [Matrix.fromBlocks_conjTranspose]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, Matrix.conjTranspose, Matrix.map_apply, Matrix.transpose_apply]

#print axioms trace_dilation_even_pow

end DilationBrick


-- ===== Inlined: schattenNorm(2n)^(2n) = trace((X Xᵀ)^n)  (proof copied from Sol_schatten_...) =====
namespace SchattenInline
open MatrixCompletion
open scoped Classical BigOperators InnerProductSpace
noncomputable section
open LinearMap

private theorem eigPowSum_eq_tracePow {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (m : ℕ) :
    LinearMap.trace 𝕜 E (T ^ m) = ∑ i, ((hT.eigenvalues hn i : 𝕜)) ^ m := by
  set b := hT.eigenvectorBasis hn with hb
  rw [LinearMap.trace_eq_sum_inner (T ^ m) b]
  apply Fintype.sum_congr
  intro i
  have hev : Module.End.HasEigenvector T (hT.eigenvalues hn i : 𝕜) (b i) :=
    hT.hasEigenvector_eigenvectorBasis hn i
  rw [hev.pow_apply m, inner_smul_right]
  have : ⟪b i, b i⟫_𝕜 = 1 := by simp [b.orthonormal.1 i]
  rw [this, mul_one]

private theorem toEuclideanLin_mul {l m k : ℕ} (A : Matrix (Fin l) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin k) ℝ) :
    Matrix.toEuclideanLin (A * B) =
      (Matrix.toEuclideanLin A) ∘ₗ (Matrix.toEuclideanLin B) := by
  ext v i
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

private theorem toEuclideanLin_pow {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (m : ℕ) :
    (Matrix.toEuclideanLin A) ^ m = Matrix.toEuclideanLin (A ^ m) := by
  induction m with
  | zero => ext v i; simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, toEuclideanLin_mul, Module.End.mul_eq_comp]

private theorem trace_col_gram_pow_eq_row_gram_pow {n1 n2 : ℕ}
    (X : RealMatrix n1 n2) (n : ℕ) (hn : 1 ≤ n) :
    Matrix.trace ((X.transpose * X) ^ n) = Matrix.trace ((X * X.transpose) ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [show 0 + m + 1 = m + 1 from by ring]
  have key : ∀ j : ℕ, (X.transpose * X) ^ (j + 1)
      = X.transpose * (X * X.transpose) ^ j * X := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      calc (X.transpose * X) ^ (k + 1 + 1)
          = (X.transpose * X) ^ (k + 1) * (X.transpose * X) := by rw [pow_succ]
        _ = (X.transpose * (X * X.transpose) ^ k * X) * (X.transpose * X) := by rw [ih]
        _ = X.transpose * ((X * X.transpose) ^ k * (X * X.transpose)) * X := by
              simp only [Matrix.mul_assoc]
        _ = X.transpose * (X * X.transpose) ^ (k + 1) * X := by
              rw [← pow_succ]
  rw [key m]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

theorem schatten_even_inline (n : ℕ) (hn : 1 ≤ n)
    {n1 n2 : ℕ} (X : RealMatrix n1 n2) :
    schattenNorm (2 * n) X ^ (2 * n) = Matrix.trace ((X * X.transpose) ^ n) := by
  rw [← trace_col_gram_pow_eq_row_gram_pow X n hn]
  set T := Matrix.toEuclideanLin X with hT
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := by simp
  set q : ℝ := 2 * (n : ℝ) with hq
  have hqpos : (0 : ℝ) < q := by rw [hq]; positivity
  have hq_natCast : ((2 * n : ℕ) : ℝ) = q := by rw [hq]; push_cast; ring
  have hsum_nonneg : (0 : ℝ) ≤ ∑ k : Fin n2, Real.rpow (T.singularValues k) q := by
    apply Finset.sum_nonneg
    intro k _
    exact Real.rpow_nonneg (T.singularValues_nonneg k) q
  have hround : schattenNorm (2 * n) X ^ (2 * n) =
      ∑ k : Fin n2, Real.rpow (T.singularValues k) q := by
    rw [schattenNorm]
    set S : ℝ := ∑ k : Fin n2, Real.rpow (T.singularValues k) q with hS
    have hSnn : (0 : ℝ) ≤ S := hsum_nonneg
    calc (Real.rpow S q⁻¹) ^ (2 * n)
        = Real.rpow (Real.rpow S q⁻¹) (((2 * n : ℕ) : ℝ)) :=
          (Real.rpow_natCast (Real.rpow S q⁻¹) (2 * n)).symm
      _ = Real.rpow (Real.rpow S q⁻¹) q := by rw [hq_natCast]
      _ = Real.rpow S (q⁻¹ * q) := (Real.rpow_mul hSnn _ _).symm
      _ = Real.rpow S 1 := by rw [inv_mul_cancel₀ (ne_of_gt hqpos)]
      _ = S := Real.rpow_one S
  rw [hround]
  have hsym : (T.adjoint ∘ₗ T).IsSymmetric := T.isSymmetric_adjoint_comp_self
  have hstep2 : ∀ k : Fin n2, Real.rpow (T.singularValues k) q =
      (hsym.eigenvalues hfin k) ^ n := by
    intro k
    have hsq : (T.singularValues k) ^ 2 = hsym.eigenvalues hfin k :=
      T.sq_singularValues_fin hfin k
    calc Real.rpow (T.singularValues k) q
        = Real.rpow (T.singularValues k) ((2 * n : ℕ) : ℝ) := by rw [hq_natCast]
      _ = (T.singularValues k) ^ (2 * n) := Real.rpow_natCast _ (2 * n)
      _ = ((T.singularValues k) ^ 2) ^ n := by rw [pow_mul]
      _ = (hsym.eigenvalues hfin k) ^ n := by rw [hsq]
  rw [Finset.sum_congr rfl (fun k _ => hstep2 k)]
  have heig : (∑ k : Fin n2, (hsym.eigenvalues hfin k) ^ n) =
      LinearMap.trace ℝ _ ((T.adjoint ∘ₗ T) ^ n) := by
    rw [eigPowSum_eq_tracePow hfin hsym n]; push_cast; rfl
  rw [heig]
  have hadj : (T.adjoint ∘ₗ T) = Matrix.toEuclideanLin (X.transpose * X) := by
    have hXt : X.transpose = X.conjTranspose := by
      ext i j; rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
    rw [hT, hXt, toEuclideanLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    try rfl
  rw [hadj, toEuclideanLin_pow, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.trace_toLin_eq]

end
end SchattenInline

-- ===== NEW BRIDGE: Tropp route to buchholz_evenq_trace_pairbound =====

namespace TroppBridge
open MatrixCompletion DilationBrick TroppSBP
open scoped BigOperators
variable {n1 n2 : ℕ}

/-- Per-coordinate scalar weight `a_c = p⁻¹·δ_{c∈Ω}·X_c`. -/
noncomputable def coeff (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) : ℝ :=
  p⁻¹ * (if c ∈ Omega then X c.1 c.2 else 0)

/-- Hermitian dilation of the single-coordinate matrix `a_c · E_{ij}`. -/
noncomputable def Hc (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) : Matrix (Fin n1 ⊕ Fin n2) (Fin n1 ⊕ Fin n2) ℝ :=
  dilation (fun a b => if a = c.1 ∧ b = c.2 then coeff Omega p X c else 0)

lemma Hc_isHermitian (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) : (Hc Omega p X c).IsHermitian :=
  dilation_isHermitian _

lemma dilation_smul (a : ℝ) (S : Matrix (Fin n1) (Fin n2) ℝ) :
    dilation (a • S) = a • dilation S := by
  unfold dilation; ext i j; cases i <;> cases j <;>
    simp [Matrix.fromBlocks, Matrix.transpose_apply]

lemma dilation_sum {κ : Type*} (s : Finset κ) (f : κ → Matrix (Fin n1) (Fin n2) ℝ) :
    dilation (∑ k ∈ s, f k) = ∑ k ∈ s, dilation (f k) := by
  classical
  induction s using Finset.induction with
  | empty => unfold dilation; ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, ← ih]
    unfold dilation; ext i j; cases i <;> cases j <;>
      simp [Matrix.fromBlocks, Matrix.transpose_apply, Matrix.add_apply]

lemma single_coord_smul (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (eps : Finset (Fin n1 × Fin n2)) (c : Fin n1 × Fin n2) :
    (sgn eps c) • (fun a b => if a = c.1 ∧ b = c.2 then coeff Omega p X c else 0 :
        Matrix (Fin n1) (Fin n2) ℝ)
      = (fun a b => if a = c.1 ∧ b = c.2 then sgn eps c * coeff Omega p X c else 0) := by
  ext a b; by_cases h : a = c.1 ∧ b = c.2 <;> simp [h]

/-- KEY IDENTITY: `Xmat (Hc) eps = dilation (rademacherSampledMatrix Ω eps p X)`. -/
lemma Xmat_Hc_eq_dilation (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (eps : Finset (Fin n1 × Fin n2)) :
    Xmat (Hc Omega p X) eps = dilation (rademacherSampledMatrix Omega eps p X) := by
  classical
  unfold Xmat Hc
  have hterm : (∑ c : Fin n1 × Fin n2, (sgn eps c) • dilation
            (fun a b => if a = c.1 ∧ b = c.2 then coeff Omega p X c else 0))
        = ∑ c : Fin n1 × Fin n2, dilation
            ((sgn eps c) • (fun a b => if a = c.1 ∧ b = c.2 then coeff Omega p X c else 0)) := by
    apply Finset.sum_congr rfl; intro c _; exact (dilation_smul _ _).symm
  rw [hterm, ← dilation_sum]
  congr 1
  ext i j
  rw [Matrix.sum_apply]
  simp only [single_coord_smul]
  rw [Finset.sum_eq_single (i, j)]
  · simp only [coeff, rademacherSampledMatrix, rademacherSign]
    by_cases hmem : (i, j) ∈ Omega
    · simp only [hmem, if_true, and_self, sgn]; ring
    · simp [hmem]
  · intro c _ hc
    have : ¬ (i = c.1 ∧ j = c.2) := by rintro ⟨rfl, rfl⟩; exact hc rfl
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

end TroppBridge

namespace TroppBridge
open MatrixCompletion DilationBrick TroppSBP
open scoped BigOperators
variable {n1 n2 : ℕ}

/-- The single-coordinate matrix `E_c` scaled by `a_c`. -/
noncomputable def Sc (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) : Matrix (Fin n1) (Fin n2) ℝ :=
  fun a b => if a = c.1 ∧ b = c.2 then coeff Omega p X c else 0

/-- `(Hc c)² = fromBlocks (Sc·Scᵀ) 0 0 (Scᵀ·Sc)`. -/
lemma Hc_sq (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) :
    (Hc Omega p X c) ^ 2
      = Matrix.fromBlocks (Sc Omega p X c * (Sc Omega p X c)ᵀ) 0 0
          ((Sc Omega p X c)ᵀ * Sc Omega p X c) := by
  unfold Hc Sc
  exact dilation_sq _

/-- `Sc·Scᵀ` is the diagonal matrix with `a_c²` at `(c.1,c.1)` and `0` elsewhere. -/
lemma Sc_mul_transpose (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) :
    Sc Omega p X c * (Sc Omega p X c)ᵀ
      = fun a a' => if a = c.1 ∧ a' = c.1 then coeff Omega p X c ^ 2 else 0 := by
  classical
  unfold Sc
  ext a a'
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_eq_single c.2]
  · by_cases h1 : a = c.1 <;> by_cases h2 : a' = c.1 <;>
      simp [h1, h2, sq]
  · intro b _ hb
    have : ¬ (a' = c.1 ∧ b = c.2) := by rintro ⟨_, rfl⟩; exact hb rfl
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `Scᵀ·Sc` is the diagonal matrix with `a_c²` at `(c.2,c.2)` and `0` elsewhere. -/
lemma transpose_mul_Sc (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) :
    (Sc Omega p X c)ᵀ * Sc Omega p X c
      = fun b b' => if b = c.2 ∧ b' = c.2 then coeff Omega p X c ^ 2 else 0 := by
  classical
  unfold Sc
  ext b b'
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_eq_single c.1]
  · by_cases h1 : b = c.2 <;> by_cases h2 : b' = c.2 <;>
      simp [h1, h2, sq]
  · intro a _ ha
    have : ¬ (a = c.1 ∧ b = c.2) := by rintro ⟨rfl, _⟩; exact ha rfl
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

end TroppBridge

namespace TroppBridge
open MatrixCompletion DilationBrick TroppSBP
open scoped BigOperators RealInnerProductSpace
variable {n1 n2 : ℕ}

/-- Eigenvalue upper bound from a scalar-shift PosSemidef witness. -/
theorem eig_le_helper {D : Type*} [Fintype D] [DecidableEq D] (A : Matrix D D ℝ) (hA : A.IsHermitian)
    (normV : ℝ) (hPSD : (normV • (1:Matrix D D ℝ) - A).PosSemidef) (i : D) :
    hA.eigenvalues i ≤ normV := by
  classical
  set v : D → ℝ := ⇑(hA.eigenvectorBasis i) with hv
  have hmul : A *ᵥ v = (hA.eigenvalues i) • v := hA.mulVec_eigenvectorBasis i
  have hone : v ⬝ᵥ v = (1:ℝ) := by
    have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 i
    have hsum : v ⬝ᵥ v = ∑ k, (hA.eigenvectorBasis i) k ^ 2 := by
      simp [dotProduct, sq, hv]
    rw [hsum]
    have hns : ‖hA.eigenvectorBasis i‖^2 = ∑ k, (hA.eigenvectorBasis i) k ^2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm] at hns; simpa using hns.symm
  have hpsd : 0 ≤ star v ⬝ᵥ ((normV • (1:Matrix D D ℝ) - A) *ᵥ v) :=
    hPSD.dotProduct_mulVec_nonneg v
  rw [sub_mulVec, smul_mulVec, Matrix.one_mulVec, hmul, dotProduct_sub,
    dotProduct_smul, dotProduct_smul] at hpsd
  simp only [star_trivial, smul_eq_mul, hone, mul_one] at hpsd
  linarith

/-- Row energy (sampled): `R i = Σ_j δ_{(i,j)∈Ω} X_{ij}²`. -/
noncomputable def rowEn (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) (i : Fin n1) : ℝ :=
  ∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0

noncomputable def colEn (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) (j : Fin n2) : ℝ :=
  ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0

/-- `Σ_c (a_c² at (c.1,c.1)) = diagonal (p⁻²·rowEn)`. -/
lemma sum_topleft (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2) :
    (∑ c : Fin n1 × Fin n2,
       (fun a a' => if a = c.1 ∧ a' = c.1 then coeff Omega p X c ^ 2 else 0 :
          Matrix (Fin n1) (Fin n1) ℝ))
      = Matrix.diagonal (fun i => p⁻¹ ^ 2 * rowEn Omega X i) := by
  classical
  ext a a'
  rw [show (∑ c : Fin n1 × Fin n2,
       (fun a a' => if a = c.1 ∧ a' = c.1 then coeff Omega p X c ^ 2 else 0 :
          Matrix (Fin n1) (Fin n1) ℝ)) a a'
        = ((∑ c : Fin n1 × Fin n2,
       (fun a a' => if a = c.1 ∧ a' = c.1 then coeff Omega p X c ^ 2 else 0 :
          Matrix (Fin n1) (Fin n1) ℝ)) a) a' from rfl, Finset.sum_apply, Finset.sum_apply,
       Matrix.diagonal_apply]
  by_cases haa' : a = a'
  · subst haa'
    rw [if_pos rfl]
    rw [Fintype.sum_prod_type]
    unfold coeff rowEn
    rw [Finset.sum_eq_single a]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      by_cases hmem : (a, j) ∈ Omega <;> simp [hmem, mul_pow] <;> ring
    · intro i _ hi; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hi, hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg haa']
    apply Finset.sum_eq_zero; intro c _
    have : ¬ (a = c.1 ∧ a' = c.1) := by rintro ⟨rfl, rfl⟩; exact haa' rfl
    simp [this]

lemma sum_botright (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2) :
    (∑ c : Fin n1 × Fin n2,
       (fun b b' => if b = c.2 ∧ b' = c.2 then coeff Omega p X c ^ 2 else 0 :
          Matrix (Fin n2) (Fin n2) ℝ))
      = Matrix.diagonal (fun j => p⁻¹ ^ 2 * colEn Omega X j) := by
  classical
  ext b b'
  rw [show (∑ c : Fin n1 × Fin n2,
       (fun b b' => if b = c.2 ∧ b' = c.2 then coeff Omega p X c ^ 2 else 0 :
          Matrix (Fin n2) (Fin n2) ℝ)) b b'
        = ((∑ c : Fin n1 × Fin n2,
       (fun b b' => if b = c.2 ∧ b' = c.2 then coeff Omega p X c ^ 2 else 0 :
          Matrix (Fin n2) (Fin n2) ℝ)) b) b' from rfl, Finset.sum_apply, Finset.sum_apply,
       Matrix.diagonal_apply]
  by_cases hbb' : b = b'
  · subst hbb'
    rw [if_pos rfl]
    rw [Fintype.sum_prod_type_right]
    unfold coeff colEn
    rw [Finset.sum_eq_single b]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      by_cases hmem : (i, b) ∈ Omega <;> simp [hmem, mul_pow] <;> ring
    · intro j _ hj; apply Finset.sum_eq_zero; intro i _; simp [Ne.symm hj, hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hbb']
    apply Finset.sum_eq_zero; intro c _
    have : ¬ (b = c.2 ∧ b' = c.2) := by rintro ⟨rfl, rfl⟩; exact hbb' rfl
    simp [this]

end TroppBridge

namespace TroppBridge
open MatrixCompletion DilationBrick TroppSBP
open scoped BigOperators
variable {n1 n2 : ℕ}

/-- `VarProxy (Hc) = fromBlocks (diag p⁻²·rowEn) 0 0 (diag p⁻²·colEn)`. -/
lemma VarProxy_Hc (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2) :
    VarProxy (Hc Omega p X)
      = Matrix.fromBlocks (Matrix.diagonal (fun i => p⁻¹ ^ 2 * rowEn Omega X i)) 0 0
          (Matrix.diagonal (fun j => p⁻¹ ^ 2 * colEn Omega X j)) := by
  classical
  unfold VarProxy
  -- each Hc c * Hc c = (Hc c)^2 = fromBlocks (Sc Scᵀ) 0 0 (Scᵀ Sc)
  have hsq : ∀ c, Hc Omega p X c * Hc Omega p X c
      = Matrix.fromBlocks (Sc Omega p X c * (Sc Omega p X c)ᵀ) 0 0
          ((Sc Omega p X c)ᵀ * Sc Omega p X c) := by
    intro c; rw [← pow_two]; exact Hc_sq Omega p X c
  rw [Finset.sum_congr rfl (fun c _ => hsq c)]
  have hsum_fb : ∀ (A : (Fin n1 × Fin n2) → Matrix (Fin n1) (Fin n1) ℝ)
      (B : (Fin n1 × Fin n2) → Matrix (Fin n1) (Fin n2) ℝ)
      (C : (Fin n1 × Fin n2) → Matrix (Fin n2) (Fin n1) ℝ)
      (Dm : (Fin n1 × Fin n2) → Matrix (Fin n2) (Fin n2) ℝ),
      (∑ c, Matrix.fromBlocks (A c) (B c) (C c) (Dm c))
        = Matrix.fromBlocks (∑ c, A c) (∑ c, B c) (∑ c, C c) (∑ c, Dm c) := by
    intro A B C Dm
    induction (Finset.univ : Finset (Fin n1 × Fin n2)) using Finset.induction with
    | empty => ext a b; rcases a with a|a <;> rcases b with b|b <;> simp [Matrix.fromBlocks]
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, Finset.sum_insert hx,
          Finset.sum_insert hx, Finset.sum_insert hx, ih]
      ext a b; rcases a with a|a <;> rcases b with b|b <;>
        simp [Matrix.fromBlocks, Matrix.add_apply]
  rw [hsum_fb]
  congr 1
  · rw [Finset.sum_congr rfl (fun c _ => Sc_mul_transpose Omega p X c)]
    exact sum_topleft Omega p X
  · simp
  · simp
  · rw [Finset.sum_congr rfl (fun c _ => transpose_mul_Sc Omega p X c)]
    exact sum_botright Omega p X

end TroppBridge

namespace TroppBridge
open MatrixCompletion DilationBrick TroppSBP
open scoped BigOperators
variable {n1 n2 : ℕ}

/-- The variance-proxy operator-norm bound (diagonal!): `normV = p⁻²·max(maxRow,maxCol)`. -/
noncomputable def normV (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2) : ℝ :=
  p⁻¹ ^ 2 * max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)

lemma rowEn_le_max (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) (i : Fin n1) :
    rowEn Omega X i ≤ max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) := by
  refine le_trans ?_ (le_max_left _ _)
  show rowEn Omega X i ≤ ⨆ i : Fin n1, ∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0
  exact le_ciSup (f := fun i : Fin n1 => ∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)
    (Finite.bddAbove_range _) i

lemma colEn_le_max (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) (j : Fin n2) :
    colEn Omega X j ≤ max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) := by
  refine le_trans ?_ (le_max_right _ _)
  show colEn Omega X j ≤ ⨆ j : Fin n2, ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0
  exact le_ciSup (f := fun j : Fin n2 => ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)
    (Finite.bddAbove_range _) j

/-- `VarProxy (Hc)` is Hermitian. -/
lemma VarProxy_Hc_isHermitian (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2) :
    (VarProxy (Hc Omega p X)).IsHermitian := by
  rw [VarProxy_Hc]
  rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
  congr 1 <;> simp [Matrix.diagonal_conjTranspose]

/-- PSD witness: `normV • 1 - VarProxy (Hc)` is PosSemidef. -/
lemma normV_smul_sub_VarProxy_posSemidef (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (X : RealMatrix n1 n2) (hp : 0 ≤ p⁻¹ ^ 2) :
    (normV Omega p X • (1 : Matrix (Fin n1 ⊕ Fin n2) (Fin n1 ⊕ Fin n2) ℝ)
      - VarProxy (Hc Omega p X)).PosSemidef := by
  classical
  rw [VarProxy_Hc]
  set nV := normV Omega p X with hnV
  set R : Fin n1 → ℝ := fun i => p⁻¹ ^ 2 * rowEn Omega X i with hR
  set C : Fin n2 → ℝ := fun j => p⁻¹ ^ 2 * colEn Omega X j with hC
  have hRle : ∀ i, R i ≤ nV := by
    intro i; rw [hR, hnV, normV]
    exact mul_le_mul_of_nonneg_left (rowEn_le_max Omega X i) hp
  have hCle : ∀ j, C j ≤ nV := by
    intro j; rw [hC, hnV, normV]
    exact mul_le_mul_of_nonneg_left (colEn_le_max Omega X j) hp
  have key : (nV • (1 : Matrix (Fin n1 ⊕ Fin n2) (Fin n1 ⊕ Fin n2) ℝ)
      - Matrix.fromBlocks (diagonal R) 0 0 (diagonal C))
      = Matrix.diagonal (Sum.elim (fun i => nV - R i) (fun j => nV - C j)) := by
    ext a b
    rcases a with a|a <;> rcases b with b|b
    · by_cases h : a = b
      · subst h; simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply]
      · simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply, h,
          fun hh : Sum.inl a = Sum.inl b => h (Sum.inl_injective hh)]
    · simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply]
    · simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply]
    · by_cases h : a = b
      · subst h; simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply]
      · simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply, h,
          fun hh : Sum.inr a = Sum.inr b => h (Sum.inr_injective hh)]
  rw [key]
  apply Matrix.PosSemidef.diagonal
  rintro (i|j)
  · show (0:ℝ) ≤ nV - R i; linarith [hRle i]
  · show (0:ℝ) ≤ nV - C j; linarith [hCle j]

/-- The eigenvalue bound feeding the Tropp engine. -/
lemma VarProxy_eig_le (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (hp : 0 ≤ p⁻¹ ^ 2) (i : Fin n1 ⊕ Fin n2) :
    (VarProxy_Hc_isHermitian Omega p X).eigenvalues i ≤ normV Omega p X :=
  eig_le_helper (VarProxy (Hc Omega p X)) (VarProxy_Hc_isHermitian Omega p X)
    (normV Omega p X) (normV_smul_sub_VarProxy_posSemidef Omega p X hp) i

end TroppBridge

namespace TroppBridge
open MatrixCompletion DilationBrick TroppSBP
open scoped BigOperators
variable {n1 n2 : ℕ}

/-- `rademacherExpectation` over `Fin n1 × Fin n2` equals `TroppSBP.Ex`. -/
lemma radExp_eq_Ex (F : Finset (Fin n1 × Fin n2) → ℝ) :
    rademacherExpectation F = Ex F := by
  unfold rademacherExpectation Ex rademacherObservationWeight
  rfl

/-- Trace of `(M Mᵀ)^n` is ≤ trace of the dilation `ℋ^{2n}` (both PSD, dilation = sum). -/
lemma trace_gram_le_trace_dilation (M : RealMatrix n1 n2) (n : ℕ) :
    Matrix.trace ((M * Mᵀ) ^ n) ≤ Matrix.trace ((dilation M) ^ (2 * n)) := by
  rw [trace_dilation_even_pow]
  have hMMt : (M * Mᵀ).PosSemidef := by
    have h : Mᵀ = Mᴴ := by ext i j; simp [Matrix.conjTranspose_apply, star_trivial]
    rw [h]; exact Matrix.posSemidef_self_mul_conjTranspose M
  have hMtM : (Mᵀ * M).PosSemidef := by
    have h : Mᵀ = Mᴴ := by ext i j; simp [Matrix.conjTranspose_apply, star_trivial]
    rw [h]; exact Matrix.posSemidef_conjTranspose_mul_self M
  have h2 : 0 ≤ Matrix.trace ((Mᵀ * M) ^ n) := (hMtM.pow n).trace_nonneg
  linarith

/-- **THE TROPP-ROUTE BOUND (variance-scale form), sorry-free, bypassing 5584a87a.**
For the Rademacher-signed sampled matrix `M = rademacherSampledMatrix Ω eps p X`:
`Ex_eps[ schattenNorm(2n)(M)^{2n} ] ≤ doubleFact(n) · varianceScale^{2n} · (n1+n2)`,
where `varianceScale = p⁻¹·√(max sampled row/col energy)`. -/
theorem tropp_even_schatten_variance_scale
    (n : Nat) (hn : 1 ≤ n)
    (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p) (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      ≤ TroppGeneral.doubleFactOdd n
          * (rademacherSampledVarianceScale Omega p X) ^ (2 * n)
          * ((n1 : ℝ) + (n2 : ℝ)) := by
  classical
  have hpinv2 : (0:ℝ) ≤ p⁻¹ ^ 2 := by positivity
  -- Step 1: rewrite schatten^{2n} = trace((M Mᵀ)^n) pointwise (uses platform brick)
  have hschatten : ∀ eps,
      schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n)
        = Matrix.trace ((rademacherSampledMatrix Omega eps p X
            * (rademacherSampledMatrix Omega eps p X).transpose) ^ n) := by
    intro eps
    exact SchattenInline.schatten_even_inline n hn (rademacherSampledMatrix Omega eps p X)
  rw [radExp_eq_Ex, Ex_congr hschatten]
  -- Step 2: trace((MMᵀ)^n) ≤ trace(ℋ^{2n}) = trace(Xmat^{2n}) pointwise
  have hdil : ∀ eps,
      Matrix.trace ((rademacherSampledMatrix Omega eps p X
          * (rademacherSampledMatrix Omega eps p X).transpose) ^ n)
        ≤ Matrix.trace ((Xmat (Hc Omega p X) eps) ^ (2 * n)) := by
    intro eps
    rw [Xmat_Hc_eq_dilation]
    exact trace_gram_le_trace_dilation (rademacherSampledMatrix Omega eps p X) n
  refine le_trans (Ex_mono _ _ hdil) ?_
  -- Step 3: Tropp engine
  have hmaxnn : 0 ≤ max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) := by
    refine le_max_of_le_left ?_
    unfold sampledRowEnergyMax
    rcases isEmpty_or_nonempty (Fin n1) with h | h
    · simp [Real.iSup_of_isEmpty]
    · exact Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => by positivity))
  have hnormVnn : 0 ≤ normV Omega p X := by unfold normV; positivity
  have htropp := TroppSBP.general_2p_trace_moment (Hc Omega p X) (Hc_isHermitian Omega p X)
    (normV Omega p X) hnormVnn
    (VarProxy_Hc_isHermitian Omega p X) (VarProxy_eig_le Omega p X hpinv2) n
  -- card (Fin n1 ⊕ Fin n2) = n1 + n2
  rw [show (Fintype.card (Fin n1 ⊕ Fin n2) : ℝ) = (n1 : ℝ) + (n2 : ℝ) from by
        rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]; push_cast; ring] at htropp
  refine le_trans htropp ?_
  -- normV^n = varianceScale^{2n}
  have hvar : (normV Omega p X) ^ n = (rademacherSampledVarianceScale Omega p X) ^ (2 * n) := by
    unfold normV rademacherSampledVarianceScale
    rw [pow_mul]; congr 1; rw [mul_pow, Real.sq_sqrt hmaxnn]
  rw [hvar]

end TroppBridge

/-! ============================================================================
    Additions for the pointwise noncommutative-Khintchine spectral-energy bound.
    Inlined: spectral≤schatten crux, rank^{1/q}≤e, doubleFact≤(2n)^n, Jensen
    power-mean, the rpow-algebra core, and the final `theorem solution`.
    ========================================================================== -/

namespace PointwiseKhintchine

open MatrixCompletion
open scoped Classical BigOperators Real Matrix.Norms.L2Operator

/-! ## Crux (A): spectralNorm ≤ schattenNorm (2n) -/

open LinearMap in
/-- `‖T v‖ ≤ σ₀ * ‖v‖` where `σ₀` is the top singular value. -/
theorem norm_apply_le_singularValues_zero_mul
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) (v : E) :
    ‖T v‖ ≤ T.singularValues 0 * ‖v‖ := by
  classical
  set n := Module.finrank ℝ E with hn
  set S : E →ₗ[ℝ] E := LinearMap.adjoint T ∘ₗ T with hS
  have hSsymm : S.IsSymmetric := T.isSymmetric_adjoint_comp_self
  set b := hSsymm.eigenvectorBasis (rfl : Module.finrank ℝ E = n) with hb
  set lam := hSsymm.eigenvalues (rfl : Module.finrank ℝ E = n) with hlam
  have hpos : S.IsPositive := T.isPositive_adjoint_comp_self
  have hlam_nonneg : ∀ i, 0 ≤ lam i := fun i =>
    hpos.nonneg_eigenvalues (rfl : Module.finrank ℝ E = n) i
  have hlam_antitone : Antitone lam := hSsymm.eigenvalues_antitone _
  set c : Fin n → ℝ := fun i => b.repr v i with hc
  have hc_inner : ∀ i, c i = (inner ℝ (b i) v : ℝ) := by
    intro i; rw [hc]; exact b.repr_apply_apply v i
  have hvnorm : ‖v‖ ^ 2 = ∑ i, (c i) ^ 2 := by
    rw [← b.sum_sq_norm_inner_right v]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc_inner i, Real.norm_eq_abs, sq_abs]
  have hTnorm : ‖T v‖ ^ 2 = ∑ i, lam i * (c i) ^ 2 := by
    have h1 : ‖T v‖ ^ 2 = (inner ℝ v (S v) : ℝ) := by
      rw [hS]
      simp only [LinearMap.comp_apply]
      rw [LinearMap.adjoint_inner_right]
      rw [real_inner_self_eq_norm_sq]
    rw [h1]
    rw [← b.sum_inner_mul_inner v (S v)]
    apply Finset.sum_congr rfl
    intro i _
    have hbi : (inner ℝ v (b i) : ℝ) = c i := by
      rw [hc_inner i, real_inner_comm]
    have hSbi : (inner ℝ (b i) (S v) : ℝ) = lam i * c i := by
      rw [← b.repr_apply_apply (S v) i]
      rw [hSsymm.eigenvectorBasis_apply_self_apply]
      simp only [hlam, hc, hb, RCLike.ofReal_real_eq_id, id_eq]
    rw [hbi, hSbi]; ring
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have : v = 0 := by
      have hsub : Subsingleton E := by
        rw [← Module.finrank_zero_iff (R := ℝ)]; rw [← hn]; exact hn0
      exact Subsingleton.elim v 0
    subst this
    simp
  · have hσsq : (T.singularValues 0) ^ 2 = lam (⟨0, hnpos⟩ : Fin n) := by
      rw [hlam]
      have := T.sq_singularValues_fin (rfl : Module.finrank ℝ E = n) (⟨0, hnpos⟩ : Fin n)
      simpa using this
    have hσ_nonneg : 0 ≤ T.singularValues 0 := T.singularValues_nonneg 0
    have hbound_sq : ‖T v‖ ^ 2 ≤ (T.singularValues 0) ^ 2 * ‖v‖ ^ 2 := by
      rw [hTnorm, hvnorm, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hci2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
      have hlam_le : lam i ≤ lam (⟨0, hnpos⟩ : Fin n) := by
        apply hlam_antitone
        exact Fin.mk_le_of_le_val (Nat.zero_le _)
      calc lam i * (c i) ^ 2
          ≤ lam (⟨0, hnpos⟩ : Fin n) * (c i) ^ 2 :=
            mul_le_mul_of_nonneg_right hlam_le hci2
        _ = (T.singularValues 0) ^ 2 * (c i) ^ 2 := by rw [hσsq]
    have hvnonneg : 0 ≤ ‖v‖ := norm_nonneg _
    have hrhs_nonneg : 0 ≤ T.singularValues 0 * ‖v‖ := by positivity
    have hsq : (‖T v‖) ^ 2 ≤ (T.singularValues 0 * ‖v‖) ^ 2 := by
      rw [mul_pow]; exact hbound_sq
    exact le_of_sq_le_sq hsq hrhs_nonneg

/-- The L2 operator norm of a finite-dim linear map is bounded by the top singular value. -/
theorem opNorm_le_singularValues_zero
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) :
    ‖LinearMap.toContinuousLinearMap T‖ ≤ T.singularValues 0 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (T.singularValues_nonneg 0)
  intro v
  exact norm_apply_le_singularValues_zero_mul T v

private lemma spectralNorm_eq_l2_opNorm
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    MatrixCompletion.spectralNorm X = ‖X‖ := by
  simp [MatrixCompletion.spectralNorm, Matrix.l2_opNorm_def]

private lemma spectralNorm_nonneg
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    0 ≤ MatrixCompletion.spectralNorm X := by
  rw [spectralNorm_eq_l2_opNorm]; exact norm_nonneg _

/-- **Crux.** `MatrixCompletion.spectralNorm M ≤ schattenNorm (2n) M` for `n ≥ 1`. -/
theorem spectral_le_schatten_2n
    {n1 n2 : ℕ} (n : ℕ) (hn : 1 ≤ n) (M : MatrixCompletion.RealMatrix n1 n2) :
    MatrixCompletion.spectralNorm M ≤ schattenNorm (2 * n : ℝ) M := by
  set T := Matrix.toEuclideanLin M with hT
  set σ₀ : ℝ := T.singularValues 0 with hσ₀
  have hσ₀nonneg : 0 ≤ σ₀ := T.singularValues_nonneg 0
  have hexp : (0 : ℝ) < 2 * n := by positivity
  have hA : MatrixCompletion.spectralNorm M ≤ σ₀ := by
    rw [MatrixCompletion.spectralNorm]
    exact opNorm_le_singularValues_zero T
  refine le_trans hA ?_
  rw [schattenNorm]
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := by simp
  rcases Nat.eq_zero_or_pos n2 with hn2 | hn2
  · have hσ₀0 : σ₀ = 0 := by
      rw [hσ₀]
      exact T.singularValues_of_finrank_le (by rw [hfr, hn2])
    rw [hσ₀0]
    apply Real.rpow_nonneg
    apply Finset.sum_nonneg
    intro k _
    exact Real.rpow_nonneg (T.singularValues_nonneg k) _
  · set q : ℝ := (2 * n : ℝ) with hq
    have hq0 : (0 : ℝ) < q := hexp
    have hsv : T.singularValues ((⟨0, hn2⟩ : Fin n2) : ℕ) = σ₀ := by rw [hσ₀]
    have hterm_nonneg : ∀ k : Fin n2,
        0 ≤ Real.rpow (T.singularValues k) q := fun k =>
      Real.rpow_nonneg (T.singularValues_nonneg k) q
    have hsum_ge :
        Real.rpow σ₀ q ≤ ∑ k : Fin n2, Real.rpow (T.singularValues k) q := by
      have hmem : (⟨0, hn2⟩ : Fin n2) ∈ (Finset.univ : Finset (Fin n2)) :=
        Finset.mem_univ _
      calc Real.rpow σ₀ q
          = Real.rpow (T.singularValues (⟨0, hn2⟩ : Fin n2)) q := by rw [hsv]
        _ ≤ ∑ k : Fin n2, Real.rpow (T.singularValues k) q :=
            Finset.single_le_sum (fun k _ => hterm_nonneg k) hmem
    have hlhs_nonneg : (0 : ℝ) ≤ Real.rpow σ₀ q := Real.rpow_nonneg hσ₀nonneg q
    have hmono :
        Real.rpow (Real.rpow σ₀ q) q⁻¹ ≤
          Real.rpow (∑ k : Fin n2, Real.rpow (T.singularValues k) q) q⁻¹ :=
      Real.rpow_le_rpow hlhs_nonneg hsum_ge (by positivity)
    have hround : Real.rpow (Real.rpow σ₀ q) q⁻¹ = σ₀ := by
      have h1 : Real.rpow (Real.rpow σ₀ q) q⁻¹ = Real.rpow σ₀ (q * q⁻¹) :=
        (Real.rpow_mul hσ₀nonneg q q⁻¹).symm
      rw [h1, mul_inv_cancel₀ (ne_of_gt hq0)]
      exact Real.rpow_one σ₀
    rw [← hround]
    exact hmono

/-! ## rank^{1/q} ≤ e -/

theorem rank_rpow_inv_le_exp_one
    (N : ℕ) (q : ℝ) (hN : 1 ≤ N) (hq : 1 ≤ q) (hlog : Real.log (N : ℝ) ≤ q) :
    Real.rpow (N : ℝ) q⁻¹ ≤ Real.exp 1 := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hNR
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  rw [show Real.rpow (N : ℝ) q⁻¹ = (N : ℝ) ^ (q⁻¹ : ℝ) from rfl,
      Real.rpow_def_of_pos hNpos]
  apply Real.exp_le_exp.mpr
  rw [mul_inv_le_iff₀ hqpos]
  simpa using hlog

/-! ## doubleFactOdd n ≤ (2n)^n -/

lemma doubleFactOdd_le_pow (n : ℕ) :
    TroppGeneral.doubleFactOdd n ≤ (2 * n : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [TroppGeneral.doubleFactOdd_succ]
    have hk0 : (0:ℝ) ≤ (2 * k : ℝ) ^ k := by positivity
    have h2k1 : (2 * (k:ℝ) + 1) ≤ (2 * (k:ℝ) + 2) := by linarith
    have hbase : (2 * (k:ℝ)) ^ k ≤ (2 * (k:ℝ) + 2) ^ k := by
      apply pow_le_pow_left₀ (by positivity); linarith
    calc (2 * (k:ℝ) + 1) * TroppGeneral.doubleFactOdd k
        ≤ (2 * (k:ℝ) + 1) * (2 * (k:ℝ)) ^ k :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ (2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 2) ^ k := by
          apply mul_le_mul h2k1 hbase hk0 (by positivity)
      _ = (2 * ((k:ℝ) + 1)) ^ (k + 1) := by
          rw [pow_succ]; push_cast; ring
      _ = (2 * ((k + 1 : ℕ) : ℝ)) ^ (k + 1) := by push_cast; ring

/-! ## Jensen power-mean for rademacherExpectation -/

lemma radWeight_sum {n1 n2 : ℕ} :
    ∑ eps : Finset (Fin n1 × Fin n2), rademacherObservationWeight eps = 1 := by
  unfold rademacherObservationWeight
  rw [Finset.sum_const]
  have hcard : (Finset.univ : Finset (Finset (Fin n1 × Fin n2))).card
      = 2 ^ Fintype.card (Fin n1 × Fin n2) := by
    rw [Finset.card_univ]; exact Fintype.card_finset
  rw [hcard, nsmul_eq_mul, div_pow, one_pow, Nat.cast_pow, Nat.cast_ofNat]
  rw [one_div, mul_inv_cancel₀]
  positivity

lemma rad_power_mean {n1 n2 : ℕ} (q K : ℝ) (hq : 0 < q) (hK : q ≤ K)
    (g : Finset (Fin n1 × Fin n2) → ℝ) (hg : ∀ eps, 0 ≤ g eps) :
    rademacherExpectation (fun eps => Real.rpow (g eps) (q / K))
      ≤ Real.rpow (rademacherExpectation g) (q / K) := by
  have hKpos : 0 < K := lt_of_lt_of_le hq hK
  have ht0 : (0:ℝ) ≤ q / K := by positivity
  have ht1 : q / K ≤ 1 := by rw [div_le_one hKpos]; exact hK
  have hconc : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (q / K)) :=
    Real.concaveOn_rpow ht0 ht1
  unfold rademacherExpectation
  have hjensen := hconc.le_map_sum
    (t := (Finset.univ : Finset (Finset (Fin n1 × Fin n2))))
    (w := rademacherObservationWeight)
    (p := g)
    (fun i _ => by unfold rademacherObservationWeight; positivity)
    (by simpa using (radWeight_sum (n1 := n1) (n2 := n2)))
    (fun i _ => hg i)
  simp only [smul_eq_mul] at hjensen
  exact hjensen

/-! ## rpow-algebra core -/

lemma rpow_core
    (q : ℕ) (n : ℕ) (hn : 1 ≤ n) (hnle : (n:ℝ) ≤ q)
    (vs D Eg Espec dfac : ℝ)
    (hvs : 0 ≤ vs) (hD : 0 ≤ D) (hEg : 0 ≤ Eg) (hdfac : 0 ≤ dfac)
    (hEspec : Espec ≤ Eg ^ ((q:ℝ) / (2 * n)))
    (hEgle : Eg ≤ dfac * vs ^ (2 * n) * D)
    (hdfacle : dfac ≤ (2 * n : ℝ) ^ n)
    (hDe : D ^ ((2 * (n:ℝ))⁻¹) ≤ Real.exp 1) :
    Espec ≤ (Real.sqrt 2 * Real.exp 1 * Real.sqrt (q:ℝ) * vs) ^ q := by
  have h2n : (0:ℝ) < 2 * n := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    linarith
  set t : ℝ := (q:ℝ) / (2 * n) with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hbasenn : 0 ≤ dfac * vs ^ (2 * n) * D := by positivity
  have hstep1 : Espec ≤ (dfac * vs ^ (2 * n) * D) ^ t := by
    refine le_trans hEspec ?_
    exact Real.rpow_le_rpow hEg hEgle ht0
  refine le_trans hstep1 ?_
  have hsplit : (dfac * vs ^ (2 * n) * D) ^ t
      = dfac ^ t * (vs ^ (2 * n)) ^ t * D ^ t := by
    rw [Real.mul_rpow (by positivity) hD]
    rw [Real.mul_rpow hdfac (by positivity)]
  rw [hsplit]
  have hvs_part : (vs ^ (2 * n)) ^ t = vs ^ q := by
    rw [← Real.rpow_natCast vs (2 * n)]
    rw [← Real.rpow_mul hvs]
    rw [← Real.rpow_natCast vs q]
    congr 1
    rw [ht]; push_cast; field_simp
  have hD_part : D ^ t ≤ Real.exp 1 ^ q := by
    have hDt : D ^ t = (D ^ ((2 * (n:ℝ))⁻¹)) ^ q := by
      rw [← Real.rpow_natCast (D ^ ((2 * (n:ℝ))⁻¹)) q]
      rw [← Real.rpow_mul hD]
      congr 1
      rw [ht]; field_simp
    rw [hDt]
    have hDbase : 0 ≤ D ^ ((2 * (n:ℝ))⁻¹) := Real.rpow_nonneg hD _
    exact pow_le_pow_left₀ hDbase hDe q
  have hdfac_part : dfac ^ t ≤ (Real.sqrt 2 * Real.sqrt (q:ℝ)) ^ q := by
    have h1 : dfac ^ t ≤ ((2 * n : ℝ) ^ n) ^ t :=
      Real.rpow_le_rpow hdfac hdfacle ht0
    refine le_trans h1 ?_
    have h2nnn : (0:ℝ) ≤ (2 * n : ℝ) := le_of_lt h2n
    have heq : ((2 * n : ℝ) ^ n) ^ t = (Real.sqrt (2 * n)) ^ q := by
      rw [← Real.rpow_natCast (2 * n : ℝ) n]
      rw [← Real.rpow_mul h2nnn]
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_natCast ((2 * (n:ℝ)) ^ (1/2 : ℝ)) q]
      rw [← Real.rpow_mul h2nnn]
      congr 1
      rw [ht]; field_simp
    rw [heq]
    have hsqrtle : Real.sqrt (2 * n) ≤ Real.sqrt (2 * (q:ℝ)) := by
      apply Real.sqrt_le_sqrt; linarith
    have hsqrt2q : Real.sqrt (2 * (q:ℝ)) = Real.sqrt 2 * Real.sqrt (q:ℝ) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [← hsqrt2q]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrtle q
  rw [hvs_part]
  calc dfac ^ t * vs ^ q * D ^ t
      ≤ (Real.sqrt 2 * Real.sqrt (q:ℝ)) ^ q * vs ^ q * Real.exp 1 ^ q := by
        apply mul_le_mul
        · apply mul_le_mul hdfac_part (le_refl _) (by positivity)
          positivity
        · exact hD_part
        · exact Real.rpow_nonneg hD t
        · positivity
    _ = (Real.sqrt 2 * Real.exp 1 * Real.sqrt (q:ℝ) * vs) ^ q := by
        rw [← mul_pow, ← mul_pow]; ring_nf

/-! ## log(n1+n2) ≤ q -/

lemma log_sum_le_q
    (β : ℝ) (hβ : 2 < β) (n1 n2 q : ℕ)
    (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hqlog : (q : ℝ) ≥ β * Real.log (↑(max n1 n2))) (hq1 : 1 ≤ q) :
    Real.log (↑(n1 + n2)) ≤ (q : ℝ) := by
  set N := max n1 n2 with hN
  have hNpos : 0 < N := lt_of_lt_of_le hn1 (Nat.le_max_left n1 n2)
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos
  have hlogN_nonneg : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNR
  -- n1 + n2 ≤ 2 N
  have hsum_le : (↑(n1 + n2) : ℝ) ≤ 2 * (N:ℝ) := by
    have : n1 + n2 ≤ 2 * N := by
      rw [hN]; omega
    calc (↑(n1 + n2) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast this
      _ = 2 * (N:ℝ) := by push_cast; ring
  have hsumpos : (0:ℝ) < (↑(n1 + n2) : ℝ) := by
    have : 0 < n1 + n2 := by omega
    exact_mod_cast this
  -- log(n1+n2) ≤ log 2 + log N
  have hlog_le : Real.log (↑(n1 + n2)) ≤ Real.log 2 + Real.log (N:ℝ) := by
    calc Real.log (↑(n1 + n2)) ≤ Real.log (2 * (N:ℝ)) :=
          Real.log_le_log hsumpos hsum_le
      _ = Real.log 2 + Real.log (N:ℝ) := by
          rw [Real.log_mul (by norm_num) (by positivity)]
  refine le_trans hlog_le ?_
  -- log 2 + log N ≤ β log N ≤ q
  rcases le_or_gt 2 N with hN2 | hN2
  · -- N ≥ 2 : log 2 ≤ log N, and (β-1) log N ≥ log N ≥ log 2
    have hlog2_le_logN : Real.log 2 ≤ Real.log (N:ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hN2
    have hkey : Real.log 2 + Real.log (N:ℝ) ≤ β * Real.log (N:ℝ) := by
      have h1 : Real.log 2 + Real.log (N:ℝ) ≤ Real.log (N:ℝ) + Real.log (N:ℝ) := by
        linarith
      have h2 : (2:ℝ) * Real.log (N:ℝ) ≤ β * Real.log (N:ℝ) := by
        apply mul_le_mul_of_nonneg_right (le_of_lt hβ) hlogN_nonneg
      linarith
    linarith [hqlog]
  · -- N = 1 : n1 = n2 = 1, log N = 0, log 2 < 1 ≤ q
    interval_cases N
    · simp only [Nat.cast_one, Real.log_one, add_zero]
      have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
        linarith
      linarith

end PointwiseKhintchine

/-! ## FINAL THEOREM -/

open PointwiseKhintchine
open MatrixCompletion
open scoped Classical BigOperators Real Matrix.Norms.L2Operator

theorem solution :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ)
        (Omega : Finset (Fin n₁ × Fin n₂)),
        0 < n₁ → 0 < n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              MatrixCompletion.spectralNorm
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ckh * Real.sqrt (q : ℝ) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X))) ^ q := by
  refine ⟨Real.sqrt 2 * Real.exp 1, by positivity, ?_⟩
  intro β hβ n₁ n₂ m q X Omega hn₁ hn₂ hq1 hqlog
  -- abbreviations
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  -- choose n = ⌈q/2⌉ = (q+1)/2
  set n : ℕ := (q + 1) / 2 with hndef
  have hn1 : 1 ≤ n := by rw [hndef]; omega
  have h2n_ge : q ≤ 2 * n := by rw [hndef]; omega
  have hnle : (n:ℝ) ≤ (q:ℝ) := by
    have : n ≤ q := by omega
    exact_mod_cast this
  have hqleR : (q:ℝ) ≤ 2 * (n:ℝ) := by
    have h := h2n_ge
    have : (q:ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_mul, Nat.cast_ofNat] at this
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  -- energies nonneg
  have hmaxnn : 0 ≤ max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) := by
    refine le_max_of_le_left ?_
    unfold sampledRowEnergyMax
    rcases isEmpty_or_nonempty (Fin n₁) with h | h
    · simp [Real.iSup_of_isEmpty]
    · exact Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => by positivity))
  -- the variance scale
  set vs : ℝ := rademacherSampledVarianceScale Omega p X with hvsdef
  have hvs_eq : vs = p⁻¹ *
      Real.sqrt (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) := by
    rw [hvsdef, rademacherSampledVarianceScale]
  have hvs_nonneg : 0 ≤ vs := by
    rw [hvs_eq]
    rcases le_or_gt 0 (p⁻¹) with hpi | hpi
    · positivity
    · -- p⁻¹ < 0 impossible since p = m/(pos) ≥ 0
      exfalso
      have hpnn : 0 ≤ p := by rw [hp]; positivity
      have : 0 ≤ p⁻¹ := inv_nonneg.mpr hpnn
      linarith
  -- RHS rewrite: Ckh·√q·p⁻¹·√max = Ckh·√q·vs
  have hRHS_eq :
      (Real.sqrt 2 * Real.exp 1 * Real.sqrt (q : ℝ) * p⁻¹ *
        Real.sqrt (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)))
      = (Real.sqrt 2 * Real.exp 1 * Real.sqrt (q:ℝ) * vs) := by
    rw [hvs_eq]; ring
  rw [hRHS_eq]
  -- split on m = 0
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0 ⇒ p = 0 ⇒ matrix is 0 ⇒ both sides 0 (q ≥ 1)
    have hp0 : p = 0 := by rw [hp, hm0]; simp
    have hMzero : ∀ eps, rademacherSampledMatrix Omega eps p X = 0 := by
      intro eps
      funext i j
      simp [rademacherSampledMatrix, hp0]
    have hLHS : rademacherExpectation
        (fun eps => MatrixCompletion.spectralNorm (rademacherSampledMatrix Omega eps p X) ^ q) = 0 := by
      have : (fun eps => MatrixCompletion.spectralNorm (rademacherSampledMatrix Omega eps p X) ^ q)
          = (fun _ : Finset (Fin n₁ × Fin n₂) => (0:ℝ)) := by
        funext eps
        rw [hMzero eps]
        rw [show MatrixCompletion.spectralNorm (0 : MatrixCompletion.RealMatrix n₁ n₂) = 0 from by
          rw [spectralNorm_eq_l2_opNorm]; simp]
        rw [zero_pow (by omega)]
      rw [this]
      unfold rademacherExpectation
      simp
    rw [hLHS]
    -- RHS: vs = 0 since p⁻¹ = 0
    have hvs0 : vs = 0 := by rw [hvs_eq, hp0]; simp
    rw [hvs0]
    rw [show (Real.sqrt 2 * Real.exp 1 * Real.sqrt (q:ℝ) * 0) = 0 from by ring]
    rw [zero_pow (by omega)]
  · -- m > 0 ⇒ p > 0
    have hppos : 0 < p := by
      rw [hp]; apply div_pos
      · exact_mod_cast hmpos
      · positivity
    -- Tropp even-moment bound
    have htropp := TroppBridge.tropp_even_schatten_variance_scale n hn1 Omega p hppos X
    set Eg : ℝ := rademacherExpectation
        (fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      with hEgdef
    set D : ℝ := (n₁ : ℝ) + (n₂ : ℝ) with hDdef
    have hDnn : 0 ≤ D := by rw [hDdef]; positivity
    -- htropp : Eg ≤ doubleFactOdd n * vs^(2n) * D
    have hEgle : Eg ≤ TroppGeneral.doubleFactOdd n * vs ^ (2 * n) * D := htropp
    have hEg_nonneg : 0 ≤ Eg := by
      rw [hEgdef]
      unfold rademacherExpectation
      apply Finset.sum_nonneg
      intro eps _
      apply mul_nonneg
      · unfold rademacherObservationWeight; positivity
      · exact (even_two_mul n).pow_nonneg _
    -- Espec := Ex[spectral^q]
    set Espec : ℝ := rademacherExpectation
        (fun eps => MatrixCompletion.spectralNorm (rademacherSampledMatrix Omega eps p X) ^ q) with hEspecdef
    -- Step 1: Espec ≤ Ex[schatten(2n)^q]
    have hstep_spec : Espec ≤ rademacherExpectation
        (fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ q) := by
      rw [hEspecdef]
      unfold rademacherExpectation
      apply Finset.sum_le_sum
      intro eps _
      apply mul_le_mul_of_nonneg_left _ (by unfold rademacherObservationWeight; positivity)
      apply pow_le_pow_left₀ (spectralNorm_nonneg _)
      exact spectral_le_schatten_2n n hn1 (rademacherSampledMatrix Omega eps p X)
    -- Step 2: Ex[schatten^q] = Ex[(schatten^{2n})^{q/(2n)}]  (rpow) ≤ Eg^{q/(2n)}  (Jensen)
    -- pointwise: schatten^q = (schatten^{2n})^{q/(2n)} as rpow
    have hpw : ∀ eps,
        (schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X)) ^ q
          = Real.rpow ((schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X)) ^ (2 * n))
              ((q:ℝ) / (2 * n)) := by
      intro eps
      set s : ℝ := schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) with hsdef
      have hsnn : 0 ≤ s := by
        rw [hsdef, schattenNorm]
        apply Real.rpow_nonneg
        apply Finset.sum_nonneg
        intro k _
        exact Real.rpow_nonneg (LinearMap.singularValues_nonneg _ k) _
      have h2npos : (0:ℝ) < 2 * (n:ℝ) := by
        have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
        linarith
      have hrhs : Real.rpow (s ^ (2 * n)) ((q:ℝ) / (2 * n))
          = Real.rpow s (((2 * n : ℕ):ℝ) * ((q:ℝ) / (2 * n))) := by
        have h1 : (s ^ (2 * n) : ℝ) = Real.rpow s ((2 * n : ℕ):ℝ) :=
          (Real.rpow_natCast s (2 * n)).symm
        rw [h1]
        exact (Real.rpow_mul hsnn ((2 * n : ℕ):ℝ) ((q:ℝ) / (2 * n))).symm
      rw [hrhs]
      rw [show ((2 * n : ℕ):ℝ) * ((q:ℝ) / (2 * n)) = (q:ℝ) by
            push_cast; field_simp]
      exact (Real.rpow_natCast s q).symm
    have hgnn : ∀ eps,
        0 ≤ (schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X)) ^ (2 * n) := by
      intro eps; exact (even_two_mul n).pow_nonneg _
    have hjensen := rad_power_mean (n1 := n₁) (n2 := n₂) (q:ℝ) (2 * (n:ℝ)) hq0R hqleR
      (fun eps => (schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X)) ^ (2 * n))
      hgnn
    -- rewrite hjensen's LHS into Ex[schatten^q] and RHS into Eg^{q/(2n)}
    have hstep_jensen :
        rademacherExpectation
          (fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ q)
          ≤ Real.rpow Eg ((q:ℝ) / (2 * n)) := by
      have hLrw : rademacherExpectation
          (fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ q)
          = rademacherExpectation
              (fun eps => Real.rpow ((schattenNorm (2 * n : ℝ)
                (rademacherSampledMatrix Omega eps p X)) ^ (2 * n)) ((q:ℝ) / (2 * n))) := by
        unfold rademacherExpectation
        apply Finset.sum_congr rfl
        intro eps _
        simp only []
        rw [hpw eps]
      rw [hLrw, hEgdef]
      exact hjensen
    -- Combine: Espec ≤ Eg^{q/(2n)}
    have hEspec_le : Espec ≤ Real.rpow Eg ((q:ℝ) / (2 * n)) :=
      le_trans hstep_spec hstep_jensen
    -- doubleFact ≤ (2n)^n
    have hdfacle : TroppGeneral.doubleFactOdd n ≤ (2 * n : ℝ) ^ n := doubleFactOdd_le_pow n
    have hdfac_nonneg : 0 ≤ TroppGeneral.doubleFactOdd n := TroppGeneral.doubleFactOdd_nonneg n
    -- D^{(2n)⁻¹} ≤ e
    have hDe : Real.rpow D ((2 * (n:ℝ))⁻¹) ≤ Real.exp 1 := by
      have hDeqcast : D = ((n₁ + n₂ : ℕ) : ℝ) := by rw [hDdef]; push_cast; ring
      rw [hDeqcast]
      have hloglesum : Real.log (↑(n₁ + n₂)) ≤ (q:ℝ) :=
        log_sum_le_q β hβ n₁ n₂ q hn₁ hn₂ hqlog hq1
      have hlogle2n : Real.log (↑(n₁ + n₂)) ≤ 2 * (n:ℝ) := le_trans hloglesum hqleR
      have h1le : 1 ≤ n₁ + n₂ := by omega
      have h1le2n : (1:ℝ) ≤ 2 * (n:ℝ) := by
        have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
        linarith
      have := rank_rpow_inv_le_exp_one (n₁ + n₂) (2 * (n:ℝ)) h1le h1le2n hlogle2n
      -- (2*(n:ℝ))⁻¹ matches
      exact this
    -- final algebra
    exact rpow_core q n hn1 hnle vs D Eg Espec (TroppGeneral.doubleFactOdd n)
      hvs_nonneg hDnn hEg_nonneg hdfac_nonneg hEspec_le hEgle hdfacle hDe

#print axioms solution
