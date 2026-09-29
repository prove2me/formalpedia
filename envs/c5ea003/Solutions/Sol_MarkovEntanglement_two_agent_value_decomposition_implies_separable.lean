-- Prove2me | solution 1 for MarkovEntanglement.two_agent_value_decomposition_implies_separable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-07T18:42:52.789851+00:00
-- url     : https://prove2.me/submissions/ed73505b-9ad7-4208-9927-f37bc4964965

import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement Matrix

/-!
# Theorem 2 (two agents): an exact value decomposition forces separability

Chen and Peng, *Multi-agent Markov Entanglement*, Theorem 2 (p. 12) and its proof in
Appendix D (pp. 33-35).

The proof runs in three moves.

1. **The hypothesis is a statement about the resolvent.**  With `A = (I - γP)⁻¹`, the
   Bellman fixed point for the reward `r` is `A r`.  Feeding in `r = 1_{a'} ⊗ 0` and
   `r = 0 ⊗ 1_{b'}` and subtracting off the (constant) value of the zero reward turns the
   decomposition hypothesis into two *slot conditions* on `A`:
   `∑_{b'} A((a,b),(a',b'))` does not depend on `b`, and `∑_{a'} A((a,b),(a',b'))` does not
   depend on `a`.

2. **The slot conditions are exactly separability of the span.**  Write `Ω` for the
   equal-row-sum subspace of a square-matrix space (Lemma 3: this is the span of the
   transition matrices).  Slot condition A says every `A`-slice of `M` lies in `Ω_A`; slot
   condition B says `M` is fixed by the projection acting in the `B` factor.  Together they
   give the *explicit* decomposition `M = ∑_{c,c'} X_{cc'} ⊗ Y_{cc'}` with
   `X_{cc'}(a,a') = M((a,c),(a',c'))` and `Y_{cc'}` the projection of the elementary matrix
   `E_{cc'}` — a two-line entrywise identity once the slot condition is available, avoiding
   the SVD of Appendix D.  Rows summing to one then upgrades the linear combination to an
   affine combination of tensor products of transition matrices.

3. **Lemma 4 transfers back to `P`.**  The span of the separable set is a finite-dimensional
   unital subalgebra of the matrix algebra, hence closed under inverses; so `A ∈ span`
   gives `A⁻¹ = I - γP ∈ span`, and `γ ≠ 0` gives `P ∈ span`.  Row sums one make it
   separable.
-/

namespace TwoAgent

variable {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]

theorem transition_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : IsTransitionMatrix A) (hB : IsTransitionMatrix B) :
    IsTransitionMatrix (A * B) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j)
  · intro i
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc ∑ k, ∑ j, A i k * B k j = ∑ k, A i k * ∑ j, B k j :=
          Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ k, A i k := Finset.sum_congr rfl fun k _ => by rw [hB.2 k, mul_one]
      _ = 1 := hA.2 i

theorem isTransitionMatrix_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsTransitionMatrix (1 : Matrix ι ι ℝ) := by
  constructor
  · intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · intro i
    simp [Matrix.one_apply]

/-- Mixed-product property in the two-agent shape. -/
theorem tensorProd_mul (A C : Matrix SA SA ℝ) (B D : Matrix SB SB ℝ) :
    tensorProd A B * tensorProd C D = tensorProd (A * C) (B * D) := by
  classical
  ext p q
  simp only [Matrix.mul_apply, tensorProd]
  rw [Fintype.sum_prod_type]
  calc ∑ u1 : SA, ∑ u2 : SB, A p.1 u1 * B p.2 u2 * (C u1 q.1 * D u2 q.2)
      = ∑ u1 : SA, ∑ u2 : SB, (A p.1 u1 * C u1 q.1) * (B p.2 u2 * D u2 q.2) :=
        Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ => by ring
    _ = (∑ u1 : SA, A p.1 u1 * C u1 q.1) * (∑ u2 : SB, B p.2 u2 * D u2 q.2) :=
        (Finset.sum_mul_sum _ _ _ _).symm

/-- An affine combination indexed by any `Fintype` witnesses separability. -/
theorem isSeparable_of_fintype {ι : Type*} [Fintype ι] {P : Matrix (SA × SB) (SA × SB) ℝ}
    (x : ι → ℝ) (PA : ι → Matrix SA SA ℝ) (PB : ι → Matrix SB SB ℝ)
    (hPA : ∀ k, IsTransitionMatrix (PA k)) (hPB : ∀ k, IsTransitionMatrix (PB k))
    (hx : ∑ k, x k = 1) (hP : P = ∑ k, x k • tensorProd (PA k) (PB k)) :
    IsSeparable P := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun n => x (e n), fun n => PA (e n), fun n => PB (e n),
    fun n => hPA _, fun n => hPB _, ?_, ?_⟩
  · rw [← hx]; exact Equiv.sum_comp e x
  · rw [hP]; exact (Equiv.sum_comp e (fun k => x k • tensorProd (PA k) (PB k))).symm

theorem isSeparable_one : IsSeparable (1 : Matrix (SA × SB) (SA × SB) ℝ) := by
  classical
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => isTransitionMatrix_one,
    fun _ => isTransitionMatrix_one, by simp, ?_⟩
  ext p q
  simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, tensorProd]
  by_cases h : p = q
  · subst h; simp [Matrix.one_apply]
  · rw [Matrix.one_apply_ne h]
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun hh => h (Prod.ext h1 hh)
      simp [Matrix.one_apply, h2]
    · simp [Matrix.one_apply, h1]

theorem isSeparable_mul {P Q : Matrix (SA × SB) (SA × SB) ℝ}
    (hP : IsSeparable P) (hQ : IsSeparable Q) : IsSeparable (P * Q) := by
  classical
  obtain ⟨K, x, A, B, hA, hB, hx, rfl⟩ := hP
  obtain ⟨L, y, C, D, hC, hD, hy, rfl⟩ := hQ
  refine isSeparable_of_fintype (ι := Fin K × Fin L)
    (fun kl => x kl.1 * y kl.2) (fun kl => A kl.1 * C kl.2) (fun kl => B kl.1 * D kl.2)
    (fun kl => transition_mul (hA _) (hC _)) (fun kl => transition_mul (hB _) (hD _)) ?_ ?_
  · rw [Fintype.sum_prod_type]
    calc ∑ k, ∑ l, x k * y l = ∑ k, x k * ∑ l, y l :=
          Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
      _ = 1 := by rw [hy]; simpa using hx
  · rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, tensorProd_mul]

theorem tensorProd_rowSum (A : Matrix SA SA ℝ) (B : Matrix SB SB ℝ)
    (hA : IsTransitionMatrix A) (hB : IsTransitionMatrix B) (p : SA × SB) :
    ∑ q : SA × SB, tensorProd A B p q = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  calc ∑ a' : SA, ∑ b' : SB, A p.1 a' * B p.2 b'
      = ∑ a' : SA, A p.1 a' * ∑ b' : SB, B p.2 b' :=
        Finset.sum_congr rfl fun a' _ => (Finset.mul_sum _ _ _).symm
    _ = 1 := by rw [hB.2 p.2]; simpa using hA.2 p.1

theorem separable_rowSum {P : Matrix (SA × SB) (SA × SB) ℝ} (hP : IsSeparable P)
    (p : SA × SB) : ∑ q : SA × SB, P p q = 1 := by
  classical
  obtain ⟨K, x, A, B, hA, hB, hx, rfl⟩ := hP
  calc ∑ q : SA × SB, (∑ k, x k • tensorProd (A k) (B k)) p q
      = ∑ q : SA × SB, ∑ k, x k * tensorProd (A k) (B k) p q :=
        Finset.sum_congr rfl fun q _ => by rw [Matrix.sum_apply]; rfl
    _ = ∑ k, x k * ∑ q : SA × SB, tensorProd (A k) (B k) p q := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ = 1 := by
        rw [← hx]
        exact Finset.sum_congr rfl fun k _ => by
          rw [tensorProd_rowSum _ _ (hA k) (hB k) p, mul_one]

theorem isSeparable_affineCombination {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (M : ι → Matrix (SA × SB) (SA × SB) ℝ) (hM : ∀ k, IsSeparable (M k))
    (hc : ∑ k, c k = 1) : IsSeparable (∑ k, c k • M k) := by
  classical
  choose K x A B hA hB hx hrep using hM
  refine isSeparable_of_fintype (ι := Σ k : ι, Fin (K k))
    (fun kj => c kj.1 * x kj.1 kj.2) (fun kj => A kj.1 kj.2) (fun kj => B kj.1 kj.2)
    (fun kj => hA kj.1 kj.2) (fun kj => hB kj.1 kj.2) ?_ ?_
  · rw [Fintype.sum_sigma]
    calc ∑ k, ∑ j, c k * x k j = ∑ k, c k * ∑ j, x k j :=
          Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
      _ = 1 := by rw [← hc]; exact Finset.sum_congr rfl fun k _ => by rw [hx k, mul_one]
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrep k, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]

/-! ### The span of the separable set -/

def SepLin (M : Matrix (SA × SB) (SA × SB) ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℝ) (T : ι → Matrix (SA × SB) (SA × SB) ℝ),
    (∀ k, IsSeparable (T k)) ∧ M = ∑ k, a k • T k

theorem SepLin.of_separable {M : Matrix (SA × SB) (SA × SB) ℝ} (h : IsSeparable M) :
    SepLin M :=
  ⟨PUnit, inferInstance, fun _ => 1, fun _ => M, fun _ => h, by simp⟩

theorem SepLin.zero : SepLin (0 : Matrix (SA × SB) (SA × SB) ℝ) :=
  ⟨Empty, inferInstance, fun k => k.elim, fun k => k.elim, fun k => k.elim, by simp⟩

theorem SepLin.add {M M' : Matrix (SA × SB) (SA × SB) ℝ} (h : SepLin M) (h' : SepLin M') :
    SepLin (M + M') := by
  obtain ⟨ι, _, a, T, hT, rfl⟩ := h
  obtain ⟨ι', _, a', T', hT', rfl⟩ := h'
  exact ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim T T',
    fun k => by cases k <;> simp [hT, hT'], by rw [Fintype.sum_sum_type]; simp⟩

theorem SepLin.smul (c : ℝ) {M : Matrix (SA × SB) (SA × SB) ℝ} (h : SepLin M) :
    SepLin (c • M) := by
  obtain ⟨ι, _, a, T, hT, rfl⟩ := h
  exact ⟨ι, inferInstance, fun k => c * a k, T, hT, by
    rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]⟩

theorem SepLin.mul {M M' : Matrix (SA × SB) (SA × SB) ℝ} (h : SepLin M) (h' : SepLin M') :
    SepLin (M * M') := by
  obtain ⟨ι, _, a, T, hT, rfl⟩ := h
  obtain ⟨ι', _, a', T', hT', rfl⟩ := h'
  refine ⟨ι × ι', inferInstance, fun kl => a kl.1 * a' kl.2,
    fun kl => T kl.1 * T' kl.2, fun kl => isSeparable_mul (hT kl.1) (hT' kl.2), ?_⟩
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    rw [smul_mul_smul_comm]

def SepSpan : Submodule ℝ (Matrix (SA × SB) (SA × SB) ℝ) where
  carrier := {M | SepLin M}
  add_mem' := SepLin.add
  zero_mem' := SepLin.zero
  smul_mem' := fun c _ h => SepLin.smul c h

/-- A linear combination of separables with row sums one is separable. -/
theorem isSeparable_of_sepLin {M : Matrix (SA × SB) (SA × SB) ℝ} (h : SepLin M)
    (p₀ : SA × SB) (hrow : ∀ p, ∑ q : SA × SB, M p q = 1) : IsSeparable M := by
  classical
  obtain ⟨ι, _, a, T, hT, rfl⟩ := h
  have hsum : ∑ k, a k = 1 := by
    have hp := hrow p₀
    calc ∑ k, a k = ∑ k, a k * ∑ q : SA × SB, T k p₀ q :=
          Finset.sum_congr rfl fun k _ => by rw [separable_rowSum (hT k) p₀, mul_one]
      _ = ∑ q : SA × SB, ∑ k, a k * T k p₀ q := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
      _ = ∑ q : SA × SB, (∑ k, a k • T k) p₀ q :=
          Finset.sum_congr rfl fun q _ => by rw [Matrix.sum_apply]; rfl
      _ = 1 := hp
  exact isSeparable_affineCombination a T hT hsum

/-- A finite-dimensional unital subalgebra is closed under inverses. -/
theorem SepLin.inv {a : Matrix (SA × SB) (SA × SB) ℝ} (ha : SepLin a)
    (hu : IsUnit a.det) : SepLin a⁻¹ := by
  classical
  set V := SepSpan (SA := SA) (SB := SB) with hV
  have haV : a ∈ V := ha
  have hone : (1 : Matrix (SA × SB) (SA × SB) ℝ) ∈ V := SepLin.of_separable isSeparable_one
  let f : V →ₗ[ℝ] V :=
    { toFun := fun v => ⟨a * (v : Matrix (SA × SB) (SA × SB) ℝ), SepLin.mul ha v.2⟩
      map_add' := fun x y => by ext : 1; simp [Matrix.mul_add]
      map_smul' := fun c x => by ext : 1; simp [Matrix.mul_smul] }
  have hinj : Function.Injective f := by
    intro x y hxy
    have h0 : a * (x : Matrix (SA × SB) (SA × SB) ℝ) = a * (y : Matrix _ _ ℝ) :=
      congrArg Subtype.val hxy
    have hxy' : (x : Matrix (SA × SB) (SA × SB) ℝ) = (y : Matrix _ _ ℝ) := by
      have := congrArg (fun M => a⁻¹ * M) h0
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hu] using this
    exact Subtype.ext hxy'
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨1, hone⟩
  have hav : a * (v : Matrix (SA × SB) (SA × SB) ℝ) = 1 := congrArg Subtype.val hv
  rw [Matrix.inv_eq_right_inv hav]
  exact v.2


/-! ### Invertibility of `1 - γ P`, and the row sums of the resolvent -/

theorem mulVec_apply' (M : Matrix (SA × SB) (SA × SB) ℝ) (w : SA × SB → ℝ) (i : SA × SB) :
    (M *ᵥ w) i = ∑ j, M i j * w j := rfl

theorem one_sub_smul_rowSum (P : Matrix (SA × SB) (SA × SB) ℝ)
    (hP : IsTransitionMatrix P) (γ : ℝ) (q : SA × SB) :
    ∑ r : SA × SB, ((1 : Matrix (SA × SB) (SA × SB) ℝ) - γ • P) q r = 1 - γ := by
  classical
  have hpt : ∀ r, ((1 : Matrix (SA × SB) (SA × SB) ℝ) - γ • P) q r
      = (1 : Matrix (SA × SB) (SA × SB) ℝ) q r - γ * P q r := fun r => rfl
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hP.2 q, mul_one]
  simp [Matrix.one_apply]

theorem isUnit_det_one_sub_smul (P : Matrix (SA × SB) (SA × SB) ℝ)
    (hP : IsTransitionMatrix P) {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ < 1) [Nonempty (SA × SB)] :
    IsUnit (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ).det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (SA × SB)) (fun i => |v i|)
      Finset.univ_nonempty
  have hfix : ∀ i, v i = γ * ∑ j, P i j * v j := by
    intro i
    have h0 : ∑ j, ((1 : Matrix (SA × SB) (SA × SB) ℝ) - γ • P) i j * v j = 0 := by
      rw [← mulVec_apply', hker]; rfl
    have hpt : ∀ j, ((1 : Matrix (SA × SB) (SA × SB) ℝ) - γ • P) i j * v j
        = (1 : Matrix (SA × SB) (SA × SB) ℝ) i j * v j - γ * (P i j * v j) := by
      intro j; simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    simp_rw [hpt] at h0
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h0
    have hid : ∑ j, (1 : Matrix (SA × SB) (SA × SB) ℝ) i j * v j = v i := by
      simp [Matrix.one_apply]
    rw [hid] at h0
    linarith
  have hbound : |v i₀| ≤ γ * |v i₀| := by
    have h1 : |∑ j, P i₀ j * v j| ≤ ∑ j, P i₀ j * |v i₀| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_of_nonneg (hP.1 i₀ j)]
      exact mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (hP.1 i₀ j)
    have h2 : ∑ j, P i₀ j * |v i₀| = |v i₀| := by
      rw [← Finset.sum_mul, hP.2 i₀, one_mul]
    calc |v i₀| = |γ * ∑ j, P i₀ j * v j| := by rw [hfix i₀]
      _ = γ * |∑ j, P i₀ j * v j| := by rw [abs_mul, abs_of_nonneg hγ]
      _ ≤ γ * |v i₀| := mul_le_mul_of_nonneg_left (h1.trans_eq h2) hγ
  have hzero : |v i₀| = 0 := by nlinarith [abs_nonneg (v i₀)]
  exact hv0 (funext fun i => by
    have h := hmax i (Finset.mem_univ i)
    rw [hzero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- Row sums of the resolvent: each equals `(1-γ)⁻¹`. -/
theorem resolvent_rowSum (P : Matrix (SA × SB) (SA × SB) ℝ)
    (hP : IsTransitionMatrix P) {γ : ℝ} (hγ1 : γ < 1)
    (hu : IsUnit (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ).det) (p : SA × SB) :
    ∑ q : SA × SB, (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ p q = (1 - γ)⁻¹ := by
  classical
  have h1γ : (1 - γ) ≠ 0 := by intro hh; linarith [sub_eq_zero.mp hh]
  have hBe : (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ) *ᵥ (fun _ => (1 : ℝ))
      = fun _ => (1 - γ) := by
    funext i
    rw [mulVec_apply']
    simpa using one_sub_smul_rowSum P hP γ i
  have hAB : (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ *ᵥ
      ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ) *ᵥ (fun _ => (1 : ℝ)))
      = fun _ => (1 : ℝ) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  rw [hBe] at hAB
  have h := congrFun hAB p
  rw [mulVec_apply'] at h
  have hmul : (∑ q : SA × SB, (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ p q) * (1 - γ) = 1 := by
    rw [Finset.sum_mul]; exact h
  field_simp
  linarith [hmul]

/-! ### The transfer from the resolvent back to `P` (the direction of Lemma 4 we use) -/

theorem separable_of_resolvent_separable [Nonempty (SA × SB)]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hsep : IsSeparable ((1 - γ) • (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹)) :
    IsSeparable P := by
  classical
  have hu : IsUnit (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ).det :=
    isUnit_det_one_sub_smul P hP (le_of_lt hγ) hγ1
  have h1γ : (1 - γ) ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  -- the resolvent itself is in the span
  have hA : SepLin ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹) := by
    have := SepLin.smul (1 - γ)⁻¹ (SepLin.of_separable hsep)
    rwa [smul_smul, inv_mul_cancel₀ h1γ, one_smul] at this
  -- hence so is its inverse `1 - γ P`
  have hinv : SepLin (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ) := by
    have h := SepLin.inv hA (Matrix.isUnit_nonsing_inv_det _ hu)
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu] at h
  -- subtract from `1` and rescale
  have hgP : SepLin (γ • P) := by
    have h := SepLin.add (SepLin.of_separable (isSeparable_one (SA := SA) (SB := SB)))
      (SepLin.smul (-1) hinv)
    have heq : γ • P
        = (1 : Matrix (SA × SB) (SA × SB) ℝ) + (-1 : ℝ) • (1 - γ • P) := by module
    rw [heq]; exact h
  have hPlin : SepLin P := by
    have h := SepLin.smul γ⁻¹ hgP
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hγ), one_smul] at h
  exact isSeparable_of_sepLin hPlin (Classical.arbitrary (SA × SB)) (fun p => hP.2 p)

/-! ### Constructive form of `Ω = {X : all row sums equal}` -/

/-- The uniform transition matrix: every entry `1 / |ι|`. -/
noncomputable def uniformT (ι : Type*) [Fintype ι] : Matrix ι ι ℝ :=
  fun _ _ => (Fintype.card ι : ℝ)⁻¹

theorem isTransitionMatrix_uniformT {ι : Type*} [Fintype ι] [Nonempty ι] :
    IsTransitionMatrix (uniformT ι) := by
  have hcard : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨fun i j => le_of_lt (inv_pos.mpr hcard), fun i => ?_⟩
  simp only [uniformT, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- A matrix whose rows all sum to `c` is a two-term combination of transition matrices
with coefficients summing to `c`. -/
theorem exists_transition_combination {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : Matrix ι ι ℝ) (c : ℝ) (hX : ∀ i, ∑ j, X i j = c) :
    ∃ (co : Bool → ℝ) (T : Bool → Matrix ι ι ℝ), (∀ d, IsTransitionMatrix (T d)) ∧
      (∑ d, co d) = c ∧ ∀ i j, X i j = ∑ d, co d * T d i j := by
  classical
  have hcard : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard
  set B : ℝ := ∑ i, ∑ j, |X i j| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set lam : ℝ := (Fintype.card ι : ℝ) * (B + |c| + 1) with hlam
  have hcl : 0 < c + lam := by
    have h1 : (1:ℝ) ≤ (Fintype.card ι : ℝ) := by
      have h : 1 ≤ Fintype.card ι := Fintype.card_pos
      exact_mod_cast h
    have hpos : (0:ℝ) < B + |c| + 1 := by linarith [abs_nonneg c]
    have hge : B + |c| + 1 ≤ lam := by rw [hlam]; nlinarith
    linarith [neg_abs_le c]
  have hlaminv : lam * (Fintype.card ι : ℝ)⁻¹ = B + |c| + 1 := by rw [hlam]; field_simp
  have hentry : ∀ i j, 0 ≤ X i j + lam * (Fintype.card ι : ℝ)⁻¹ := by
    intro i j
    have h1 : |X i j| ≤ ∑ j', |X i j'| :=
      Finset.single_le_sum (f := fun j' => |X i j'|) (fun j' _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h2 : (∑ j', |X i j'|) ≤ B :=
      Finset.single_le_sum (f := fun i' => ∑ j', |X i' j'|)
        (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i)
    have hxij : |X i j| ≤ B := le_trans h1 h2
    rw [hlaminv]
    linarith [neg_abs_le (X i j), abs_nonneg c]
  refine ⟨fun d => cond d (c + lam) (-lam),
    fun d => cond d ((c + lam)⁻¹ • (X + lam • uniformT ι)) (uniformT ι), ?_, ?_, ?_⟩
  · intro d
    cases d with
    | false => simpa using (isTransitionMatrix_uniformT (ι := ι))
    | true =>
      simp only [Bool.cond_true]
      constructor
      · intro i j
        have hnn : (0:ℝ) ≤ (c + lam)⁻¹ := le_of_lt (inv_pos.mpr hcl)
        exact mul_nonneg hnn (by simpa [uniformT] using hentry i j)
      · intro i
        have hrow : ∑ j, (X + lam • uniformT ι) i j = c + lam := by
          simp only [Matrix.add_apply, Matrix.smul_apply, uniformT, smul_eq_mul]
          rw [Finset.sum_add_distrib, hX i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
        show ∑ j, (c + lam)⁻¹ * (X + lam • uniformT ι) i j = 1
        rw [← Finset.mul_sum, hrow, inv_mul_cancel₀ (ne_of_gt hcl)]
  · rw [Fintype.sum_bool]
    simp only [Bool.cond_true, Bool.cond_false]
    ring
  · intro i j
    rw [Fintype.sum_bool]
    simp only [Bool.cond_true, Bool.cond_false]
    show X i j = (c + lam) * ((c + lam)⁻¹ * (X i j + lam * (Fintype.card ι : ℝ)⁻¹))
        + -lam * (Fintype.card ι : ℝ)⁻¹
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcl), one_mul]
    ring

/-! ### The slot criterion: both marginal conditions force separability -/

/-- The `(c,c')`-slice of `M` in the `A` factor. -/
def slotX (M : Matrix (SA × SB) (SA × SB) ℝ) (cc : SB × SB) : Matrix SA SA ℝ :=
  fun a a' => M (a, cc.1) (a', cc.2)

/-- The image of the elementary matrix `E_{cc'}` under the projection of `Matrix SB SB ℝ`
onto the equal-row-sum subspace. -/
noncomputable def slotY (SB : Type*) [Fintype SB] [DecidableEq SB] (cc : SB × SB) :
    Matrix SB SB ℝ :=
  fun b b' => (if cc.1 = b then (1:ℝ) else 0) * (if cc.2 = b' then (1:ℝ) else 0)
    - (Fintype.card SB : ℝ)⁻¹ * (if cc.1 = b then (1:ℝ) else 0)
    + ((Fintype.card SB : ℝ) * (Fintype.card SB : ℝ))⁻¹

theorem sum2_sub_add {ι κ : Type*} [Fintype ι] [Fintype κ] (F G H : ι → κ → ℝ) :
    (∑ c : ι, ∑ c' : κ, (F c c' - G c c' + H c c'))
      = (∑ c : ι, ∑ c' : κ, F c c') - (∑ c : ι, ∑ c' : κ, G c c')
        + (∑ c : ι, ∑ c' : κ, H c c') := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum_mul_indicator {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (t : ι) :
    (∑ c : ι, f c * (if c = t then (1:ℝ) else 0)) = f t := by
  simp

theorem slotY_rowSum [Nonempty SB] (cc : SB × SB) (b : SB) :
    ∑ b', slotY SB cc b b' = (Fintype.card SB : ℝ)⁻¹ := by
  classical
  have hcard : (0:ℝ) < (Fintype.card SB : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcne : (Fintype.card SB : ℝ) ≠ 0 := ne_of_gt hcard
  have h1 : ∑ b' : SB, (if cc.1 = b then (1:ℝ) else 0) * (if cc.2 = b' then (1:ℝ) else 0)
      = (if cc.1 = b then (1:ℝ) else 0) := by
    rw [← Finset.mul_sum]; simp
  have h2 : ∑ _b' : SB, (Fintype.card SB : ℝ)⁻¹ * (if cc.1 = b then (1:ℝ) else 0)
      = (if cc.1 = b then (1:ℝ) else 0) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hcne, one_mul]
  have h3 : ∑ _b' : SB, ((Fintype.card SB : ℝ) * (Fintype.card SB : ℝ))⁻¹
      = (Fintype.card SB : ℝ)⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  show ∑ b' : SB, ((if cc.1 = b then (1:ℝ) else 0) * (if cc.2 = b' then (1:ℝ) else 0)
      - (Fintype.card SB : ℝ)⁻¹ * (if cc.1 = b then (1:ℝ) else 0)
      + ((Fintype.card SB : ℝ) * (Fintype.card SB : ℝ))⁻¹) = (Fintype.card SB : ℝ)⁻¹
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3]
  ring

/-- The slot-`B` condition makes `M` the explicit sum `∑_{c,c'} X_{cc'} ⊗ Y_{cc'}`. -/
theorem slot_identity [Nonempty SB] (M : Matrix (SA × SB) (SA × SB) ℝ)
    (hslotB : ∀ (a a' : SA) (b₁ b₂ : SB),
      (∑ y : SB, M (a, b₁) (a', y)) = ∑ y : SB, M (a, b₂) (a', y))
    (a : SA) (b : SB) (a' : SA) (b' : SB) :
    M (a, b) (a', b') = ∑ cc : SB × SB, slotX M cc a a' * slotY SB cc b b' := by
  classical
  have hcard : (0:ℝ) < (Fintype.card SB : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcne : (Fintype.card SB : ℝ) ≠ 0 := ne_of_gt hcard
  rw [Fintype.sum_prod_type]
  have hsummand : ∀ c c' : SB, slotX M (c, c') a a' * slotY SB (c, c') b b'
      = M (a, c) (a', c') * ((if c = b then (1:ℝ) else 0) * (if c' = b' then (1:ℝ) else 0))
        - M (a, c) (a', c') * ((Fintype.card SB : ℝ)⁻¹ * (if c = b then (1:ℝ) else 0))
        + M (a, c) (a', c') * ((Fintype.card SB : ℝ) * (Fintype.card SB : ℝ))⁻¹ := by
    intro c c'
    show M (a, c) (a', c') * (_ - _ + _) = _
    ring
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => hsummand c c']
  rw [sum2_sub_add]
  -- the three pieces
  have hg : ∀ c : SB, (∑ y : SB, M (a, c) (a', y)) = ∑ y : SB, M (a, b) (a', y) :=
    fun c => hslotB a a' c b
  have hS1 : (∑ c : SB, ∑ c' : SB,
      M (a, c) (a', c') * ((if c = b then (1:ℝ) else 0) * (if c' = b' then (1:ℝ) else 0)))
      = M (a, b) (a', b') := by
    have inner : ∀ c : SB, (∑ c' : SB,
        M (a, c) (a', c') * ((if c = b then (1:ℝ) else 0) * (if c' = b' then (1:ℝ) else 0)))
        = M (a, c) (a', b') * (if c = b then (1:ℝ) else 0) := by
      intro c
      rw [Finset.sum_congr rfl fun c' _ =>
        (by ring : M (a, c) (a', c') * ((if c = b then (1:ℝ) else 0) * (if c' = b' then (1:ℝ) else 0))
          = (M (a, c) (a', c') * (if c = b then (1:ℝ) else 0)) * (if c' = b' then (1:ℝ) else 0))]
      exact sum_mul_indicator (fun y => M (a, c) (a', y) * (if c = b then (1:ℝ) else 0)) b'
    rw [Finset.sum_congr rfl fun c _ => inner c]
    exact sum_mul_indicator (fun c => M (a, c) (a', b')) b
  have hS2 : (∑ c : SB, ∑ c' : SB,
      M (a, c) (a', c') * ((Fintype.card SB : ℝ)⁻¹ * (if c = b then (1:ℝ) else 0)))
      = (Fintype.card SB : ℝ)⁻¹ * (∑ y : SB, M (a, b) (a', y)) := by
    have inner : ∀ c : SB, (∑ c' : SB,
        M (a, c) (a', c') * ((Fintype.card SB : ℝ)⁻¹ * (if c = b then (1:ℝ) else 0)))
        = ((Fintype.card SB : ℝ)⁻¹ * (∑ y : SB, M (a, c) (a', y)))
          * (if c = b then (1:ℝ) else 0) := by
      intro c
      rw [← Finset.sum_mul]
      ring
    rw [Finset.sum_congr rfl fun c _ => inner c]
    exact sum_mul_indicator
      (fun c => (Fintype.card SB : ℝ)⁻¹ * (∑ y : SB, M (a, c) (a', y))) b
  have hS3 : (∑ c : SB, ∑ c' : SB,
      M (a, c) (a', c') * ((Fintype.card SB : ℝ) * (Fintype.card SB : ℝ))⁻¹)
      = (Fintype.card SB : ℝ) * ((∑ y : SB, M (a, b) (a', y))
          * ((Fintype.card SB : ℝ) * (Fintype.card SB : ℝ))⁻¹) := by
    have inner : ∀ c : SB, (∑ c' : SB,
        M (a, c) (a', c') * ((Fintype.card SB : ℝ) * (Fintype.card SB : ℝ))⁻¹)
        = (∑ y : SB, M (a, b) (a', y)) * ((Fintype.card SB : ℝ) * (Fintype.card SB : ℝ))⁻¹ := by
      intro c
      rw [← Finset.sum_mul, hg c]
    rw [Finset.sum_congr rfl fun c _ => inner c, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [hS1, hS2, hS3]
  field_simp
  ring

/-- **The slot criterion.** If summing out either agent's target coordinate gives something
independent of that agent's source coordinate, and the rows sum to one, then `M` is
separable. -/
theorem separable_of_slots [Nonempty SA] [Nonempty SB]
    (M : Matrix (SA × SB) (SA × SB) ℝ)
    (hslotA : ∀ (a₁ a₂ : SA) (b b' : SB),
      (∑ x : SA, M (a₁, b) (x, b')) = ∑ x : SA, M (a₂, b) (x, b'))
    (hslotB : ∀ (a a' : SA) (b₁ b₂ : SB),
      (∑ y : SB, M (a, b₁) (a', y)) = ∑ y : SB, M (a, b₂) (a', y))
    (hrow : ∀ p, ∑ q : SA × SB, M p q = 1) :
    IsSeparable M := by
  classical
  obtain ⟨a₀⟩ := (inferInstance : Nonempty SA)
  obtain ⟨b₀⟩ := (inferInstance : Nonempty SB)
  have hXc : ∀ cc : SB × SB, ∀ a : SA,
      ∑ a', slotX M cc a a' = ∑ a', slotX M cc a₀ a' := fun cc a => hslotA a a₀ cc.1 cc.2
  choose coX TX hTX hcoX hXrep using fun cc : SB × SB =>
    exists_transition_combination (slotX M cc) (∑ a', slotX M cc a₀ a') (hXc cc)
  choose coY TY hTY hcoY hYrep using fun cc : SB × SB =>
    exists_transition_combination (slotY SB cc) (Fintype.card SB : ℝ)⁻¹ (slotY_rowSum cc)
  -- the row sum of `M` in terms of the slice row sums
  have hbase : ∑ q : SA × SB, M (a₀, b₀) q
      = ∑ cc : SB × SB, (∑ a', slotX M cc a₀ a') * (Fintype.card SB : ℝ)⁻¹ := by
    rw [Fintype.sum_prod_type]
    calc ∑ a' : SA, ∑ b' : SB, M (a₀, b₀) (a', b')
        = ∑ a' : SA, ∑ b' : SB, ∑ cc : SB × SB, slotX M cc a₀ a' * slotY SB cc b₀ b' :=
          Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ =>
            slot_identity M hslotB a₀ b₀ a' b'
      _ = ∑ a' : SA, ∑ cc : SB × SB, ∑ b' : SB,
            slotX M cc a₀ a' * slotY SB cc b₀ b' :=
          Finset.sum_congr rfl fun a' _ => Finset.sum_comm
      _ = ∑ cc : SB × SB, ∑ a' : SA, ∑ b' : SB,
            slotX M cc a₀ a' * slotY SB cc b₀ b' := Finset.sum_comm
      _ = ∑ cc : SB × SB, (∑ a', slotX M cc a₀ a') * (Fintype.card SB : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl fun cc _ => ?_
          rw [← slotY_rowSum cc b₀, Finset.sum_mul_sum]
  have hprod : ∑ cc : SB × SB,
      (∑ a', slotX M cc a₀ a') * (Fintype.card SB : ℝ)⁻¹ = 1 := by
    rw [← hbase]; exact hrow (a₀, b₀)
  refine isSeparable_of_fintype (ι := (SB × SB) × Bool × Bool)
    (fun k => coX k.1 k.2.1 * coY k.1 k.2.2)
    (fun k => TX k.1 k.2.1) (fun k => TY k.1 k.2.2)
    (fun k => hTX _ _) (fun k => hTY _ _) ?_ ?_
  · rw [Fintype.sum_prod_type, ← hprod]
    refine Finset.sum_congr rfl fun cc _ => ?_
    rw [Fintype.sum_prod_type, ← hcoX cc, ← hcoY cc, Finset.sum_mul_sum]
  · ext p q
    rw [Matrix.sum_apply, Fintype.sum_prod_type]
    have hM : M p q = ∑ cc : SB × SB, slotX M cc p.1 q.1 * slotY SB cc p.2 q.2 :=
      slot_identity M hslotB p.1 p.2 q.1 q.2
    rw [hM]
    refine Finset.sum_congr rfl fun cc _ => ?_
    rw [hXrep cc p.1 q.1, hYrep cc p.2 q.2, Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show _ = (coX cc i * coY cc j) * (TX cc i p.1 q.1 * TY cc j p.2 q.2)
    ring

/-! ### From the value decomposition to the slot conditions -/

/-- The resolvent supplies a Bellman fixed point for every reward. -/
theorem isBellmanQ_resolvent (P : Matrix (SA × SB) (SA × SB) ℝ) {γ : ℝ}
    (hu : IsUnit (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ).det) (r : SA × SB → ℝ) :
    IsBellmanQ P r γ ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ *ᵥ r) := by
  classical
  intro i
  have h : (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ) *ᵥ
      ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ *ᵥ r) = r := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hi := congrFun h i
  rw [mulVec_apply'] at hi
  have hexp : ∑ j, (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ) i j *
      ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ *ᵥ r) j
      = ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ *ᵥ r) i
        - γ * ∑ j, P i j * ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ *ᵥ r) j := by
    have hpt : ∀ j, (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ) i j *
        ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ *ᵥ r) j
        = (1 : Matrix (SA × SB) (SA × SB) ℝ) i j *
            ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ *ᵥ r) j
          - γ * (P i j * ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹ *ᵥ r) j) := by
      intro j; simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    simp [Matrix.one_apply]
  rw [hexp] at hi
  linarith

/-- The value at the reward `1_{a'}⊗0` reads off the `B`-marginal of the resolvent. -/
theorem mulVec_indicatorA (A : Matrix (SA × SB) (SA × SB) ℝ) (p : SA × SB) (a' : SA) :
    (A *ᵥ (fun q : SA × SB => (if q.1 = a' then (1:ℝ) else 0) + (0 : SB → ℝ) q.2)) p
      = ∑ y : SB, A p (a', y) := by
  classical
  rw [mulVec_apply', Fintype.sum_prod_type]
  have step : ∀ x : SA, (∑ y : SB, A p (x, y) *
      ((if (x, y).1 = a' then (1:ℝ) else 0) + (0 : SB → ℝ) (x, y).2))
      = (∑ y : SB, A p (x, y)) * (if x = a' then (1:ℝ) else 0) := by
    intro x
    rw [Finset.sum_congr rfl fun y _ =>
      (by simp : A p (x, y) * ((if (x, y).1 = a' then (1:ℝ) else 0) + (0 : SB → ℝ) (x, y).2)
        = A p (x, y) * (if x = a' then (1:ℝ) else 0))]
    rw [← Finset.sum_mul]
  rw [Finset.sum_congr rfl fun x _ => step x]
  exact sum_mul_indicator (fun x => ∑ y : SB, A p (x, y)) a'

/-- The value at the reward `0⊗1_{b'}` reads off the `A`-marginal of the resolvent. -/
theorem mulVec_indicatorB (A : Matrix (SA × SB) (SA × SB) ℝ) (p : SA × SB) (b' : SB) :
    (A *ᵥ (fun q : SA × SB => (0 : SA → ℝ) q.1 + (if q.2 = b' then (1:ℝ) else 0))) p
      = ∑ x : SA, A p (x, b') := by
  classical
  rw [mulVec_apply', Fintype.sum_prod_type]
  have step : ∀ x : SA, (∑ y : SB, A p (x, y) *
      ((0 : SA → ℝ) (x, y).1 + (if (x, y).2 = b' then (1:ℝ) else 0)))
      = A p (x, b') := by
    intro x
    rw [Finset.sum_congr rfl fun y _ =>
      (by simp : A p (x, y) * ((0 : SA → ℝ) (x, y).1 + (if (x, y).2 = b' then (1:ℝ) else 0))
        = A p (x, y) * (if y = b' then (1:ℝ) else 0))]
    exact sum_mul_indicator (fun y => A p (x, y)) b'
  rw [Finset.sum_congr rfl fun x _ => step x]

/-! ### Theorem 2, two agents -/

theorem two_agent_value_decomposition_implies_separable
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hdec : ∃ (QA : (SA → ℝ) → (SA → ℝ)) (QB : (SB → ℝ) → (SB → ℝ)),
      ∀ (rA : SA → ℝ) (rB : SB → ℝ) (Q : SA × SB → ℝ),
        IsBellmanQ P (fun p => rA p.1 + rB p.2) γ Q →
          ∀ p : SA × SB, Q p = QA rA p.1 + QB rB p.2) :
    IsSeparable P := by
  classical
  by_cases hne : Nonempty (SA × SB)
  case neg =>
    -- an empty joint state space: every matrix is trivially separable
    have hemp : IsEmpty (SA × SB) := not_nonempty_iff.mp hne
    have hTA : ∃ T : Matrix SA SA ℝ, IsTransitionMatrix T := by
      by_cases h : Nonempty SA
      · exact ⟨uniformT SA, isTransitionMatrix_uniformT⟩
      · have : IsEmpty SA := not_nonempty_iff.mp h
        exact ⟨0, ⟨fun i => this.elim i, fun i => this.elim i⟩⟩
    have hTB : ∃ T : Matrix SB SB ℝ, IsTransitionMatrix T := by
      by_cases h : Nonempty SB
      · exact ⟨uniformT SB, isTransitionMatrix_uniformT⟩
      · have : IsEmpty SB := not_nonempty_iff.mp h
        exact ⟨0, ⟨fun i => this.elim i, fun i => this.elim i⟩⟩
    obtain ⟨TA, hTA'⟩ := hTA
    obtain ⟨TB, hTB'⟩ := hTB
    exact ⟨1, fun _ => 1, fun _ => TA, fun _ => TB, fun _ => hTA', fun _ => hTB', by simp,
      by ext p q; exact hemp.elim p⟩
  case pos =>
  haveI : Nonempty (SA × SB) := hne
  haveI hnA : Nonempty SA := ⟨(Classical.arbitrary (SA × SB)).1⟩
  haveI hnB : Nonempty SB := ⟨(Classical.arbitrary (SA × SB)).2⟩
  have hu : IsUnit (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ).det :=
    isUnit_det_one_sub_smul P hP (le_of_lt hγ) hγ1
  have h1γ : (1 - γ) ≠ 0 := by intro hh; linarith [sub_eq_zero.mp hh]
  obtain ⟨QA, QB, hQ⟩ := hdec
  -- the zero reward pins `QA 0` and `QB 0` to opposite constants
  have hzero : ∀ (a : SA) (b : SB), QA 0 a + QB 0 b = 0 := by
    intro a b
    have hb : IsBellmanQ P (fun p => (0 : SA → ℝ) p.1 + (0 : SB → ℝ) p.2) γ
        (fun _ => (0:ℝ)) := by intro i; simp
    exact (hQ 0 0 (fun _ => 0) hb (a, b)).symm
  have hzA : ∀ a₁ a₂ : SA, QA 0 a₁ = QA 0 a₂ := by
    intro a₁ a₂
    have h1 := hzero a₁ (Classical.arbitrary SB)
    have h2 := hzero a₂ (Classical.arbitrary SB)
    linarith
  have hzB : ∀ b₁ b₂ : SB, QB 0 b₁ = QB 0 b₂ := by
    intro b₁ b₂
    have h1 := hzero (Classical.arbitrary SA) b₁
    have h2 := hzero (Classical.arbitrary SA) b₂
    linarith
  -- slot condition B: summing out agent B's target coordinate is independent of `b`
  have hslotB : ∀ (a a' : SA) (b₁ b₂ : SB),
      (∑ y : SB, ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹) (a, b₁) (a', y))
        = ∑ y : SB, ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹) (a, b₂) (a', y) := by
    intro a a' b₁ b₂
    set rA : SA → ℝ := fun x => if x = a' then (1:ℝ) else 0 with hrA
    have hb := isBellmanQ_resolvent P hu (fun q : SA × SB => rA q.1 + (0 : SB → ℝ) q.2)
    have e₁ := hQ rA 0 _ hb (a, b₁)
    have e₂ := hQ rA 0 _ hb (a, b₂)
    rw [mulVec_indicatorA] at e₁ e₂
    rw [e₁, e₂, hzB b₁ b₂]
  -- slot condition A: summing out agent A's target coordinate is independent of `a`
  have hslotA : ∀ (a₁ a₂ : SA) (b b' : SB),
      (∑ x : SA, ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹) (a₁, b) (x, b'))
        = ∑ x : SA, ((1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹) (a₂, b) (x, b') := by
    intro a₁ a₂ b b'
    set rB : SB → ℝ := fun y => if y = b' then (1:ℝ) else 0 with hrB
    have hb := isBellmanQ_resolvent P hu (fun q : SA × SB => (0 : SA → ℝ) q.1 + rB q.2)
    have e₁ := hQ 0 rB _ hb (a₁, b)
    have e₂ := hQ 0 rB _ hb (a₂, b)
    rw [mulVec_indicatorB] at e₁ e₂
    rw [e₁, e₂, hzA a₁ a₂]
  -- the rescaled resolvent is separable
  have hsep : IsSeparable ((1 - γ) • (1 - γ • P : Matrix (SA × SB) (SA × SB) ℝ)⁻¹) := by
    refine separable_of_slots _ ?_ ?_ ?_
    · intro a₁ a₂ b b'
      show ∑ x : SA, (1 - γ) * _ = ∑ x : SA, (1 - γ) * _
      rw [← Finset.mul_sum, ← Finset.mul_sum, hslotA a₁ a₂ b b']
    · intro a a' b₁ b₂
      show ∑ y : SB, (1 - γ) * _ = ∑ y : SB, (1 - γ) * _
      rw [← Finset.mul_sum, ← Finset.mul_sum, hslotB a a' b₁ b₂]
    · intro p
      show ∑ q : SA × SB, (1 - γ) * _ = 1
      rw [← Finset.mul_sum, resolvent_rowSum P hP hγ1 hu p, mul_inv_cancel₀ h1γ]
  exact separable_of_resolvent_separable P hP hγ hγ1 hsep

end TwoAgent

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hdec : ∃ (QA : (SA → ℝ) → (SA → ℝ)) (QB : (SB → ℝ) → (SB → ℝ)),
      ∀ (rA : SA → ℝ) (rB : SB → ℝ) (Q : SA × SB → ℝ),
        IsBellmanQ P (fun p => rA p.1 + rB p.2) γ Q →
          ∀ p : SA × SB, Q p = QA rA p.1 + QB rB p.2) :
    IsSeparable P :=
  TwoAgent.two_agent_value_decomposition_implies_separable P hP γ hγ hγ1 hdec
