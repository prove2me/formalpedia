-- Prove2me | solution 1 for ConvexOptimization.sdp_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T05:09:51.755271+00:00
-- url     : https://prove2.me/submissions/2a1cff7a-113e-4671-940b-59c19f410f92

import Mathlib
import Definitions.Def_dualCone
import Theorems.Thm_ConvexOptimization_conic_slater_strong_duality

open scoped RealInnerProductSpace ENNReal MatrixOrder
open MeasureTheory
open Matrix

namespace SDPAux

variable {nn : ℕ}

/-! ### Symmetric matrices, entrywise -/

theorem isSymm_apply {M : Matrix (Fin nn) (Fin nn) ℝ} (h : M.IsSymm) (i j : Fin nn) :
    M j i = M i j := congrFun (congrFun h i) j

theorem isSymm_of_apply {M : Matrix (Fin nn) (Fin nn) ℝ} (h : ∀ i j, M j i = M i j) :
    M.IsSymm := by
  ext i j; exact h i j

/-- For a symmetric `N`, `tr (M N)` is the entrywise pairing of `M` and `N`. -/
theorem trace_mul_eq_sum (M N : Matrix (Fin nn) (Fin nn) ℝ) (hN : N.IsSymm) :
    (M * N).trace = ∑ i, ∑ j, M i j * N i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [isSymm_apply hN i j]

/-! ### Identifying matrices with a Euclidean space -/

/-- The coordinatewise identification of `nn × nn` matrices with `ℝ^(nn·nn)`, so that
the cone of positive semidefinite matrices becomes a cone in a Euclidean space of the
shape required by the cone-programming theorem. -/
noncomputable def toE (M : Matrix (Fin nn) (Fin nn) ℝ) :
    EuclideanSpace ℝ (Fin (nn * nn)) :=
  WithLp.toLp 2 (fun k => M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

/-- The inverse identification. -/
def ofE (y : EuclideanSpace ℝ (Fin (nn * nn))) : Matrix (Fin nn) (Fin nn) ℝ :=
  Matrix.of fun i j => y (finProdFinEquiv (i, j))

@[simp] theorem ofE_toE (M : Matrix (Fin nn) (Fin nn) ℝ) : ofE (toE M) = M := by
  ext i j
  show M (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = M i j
  rw [Equiv.symm_apply_apply]

@[simp] theorem toE_ofE (y : EuclideanSpace ℝ (Fin (nn * nn))) : toE (ofE y) = y := by
  ext k
  show y (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = y k
  rw [Prod.mk.eta, Equiv.apply_symm_apply]

theorem toE_add (M N : Matrix (Fin nn) (Fin nn) ℝ) : toE (M + N) = toE M + toE N := by
  ext p; rfl

theorem toE_smul (c : ℝ) (M : Matrix (Fin nn) (Fin nn) ℝ) : toE (c • M) = c • toE M := by
  ext p; rfl

theorem toE_neg (M : Matrix (Fin nn) (Fin nn) ℝ) : toE (-M) = -toE M := by
  ext p; rfl

theorem toE_sub (M N : Matrix (Fin nn) (Fin nn) ℝ) : toE (M - N) = toE M - toE N := by
  ext p; rfl

theorem toE_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin nn) (Fin nn) ℝ) :
    toE (∑ i ∈ s, f i) = ∑ i ∈ s, toE (f i) := by
  classical
  induction s using Finset.induction with
  | empty => ext p; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, toE_add, ih]

theorem inner_toE (M N : Matrix (Fin nn) (Fin nn) ℝ) :
    ⟪toE M, toE N⟫ = ∑ i, ∑ j, M i j * N i j := by
  have key : ∑ k : Fin (nn * nn), (inner ℝ ((toE M) k) ((toE N) k) : ℝ)
      = ∑ p : Fin nn × Fin nn, M p.1 p.2 * N p.1 p.2 :=
    Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun k => by simp [toE, mul_comm])
  rw [PiLp.inner_apply, key, Fintype.sum_prod_type]

/-! ### Quadratic forms -/

theorem quad_eq_sum (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, M i j * (x i * x j) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem quad_eq_inner (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ⟪toE M, toE (Matrix.vecMulVec x x)⟫ := by
  rw [inner_toE, quad_eq_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl

theorem vecMulVec_isSymm (x : Fin nn → ℝ) : (Matrix.vecMulVec x x).IsSymm :=
  isSymm_of_apply fun i j => by simp [Matrix.vecMulVec_apply, mul_comm]

theorem dotProduct_self_nonneg (x : Fin nn → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem dotProduct_self_pos {x : Fin nn → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  rw [dotProduct]
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact mul_self_pos.mpr (by simpa using hi)

theorem norm_toE_vecMulVec (x : Fin nn → ℝ) :
    ‖toE (Matrix.vecMulVec x x)‖ = x ⬝ᵥ x := by
  have hsq : ‖toE (Matrix.vecMulVec x x)‖ ^ 2 = (x ⬝ᵥ x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toE]
    have h1 : ∀ i j : Fin nn, Matrix.vecMulVec x x i j * Matrix.vecMulVec x x i j
        = (x i * x i) * (x j * x j) := by
      intro i j; simp [Matrix.vecMulVec_apply]; ring
    calc ∑ i, ∑ j, Matrix.vecMulVec x x i j * Matrix.vecMulVec x x i j
        = ∑ i, ∑ j, (x i * x i) * (x j * x j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
      _ = (∑ i, x i * x i) * (∑ j, x j * x j) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ = (x ⬝ᵥ x) ^ 2 := by rw [dotProduct]; ring
  have h1 : (0 : ℝ) ≤ ‖toE (Matrix.vecMulVec x x)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ x ⬝ᵥ x := dotProduct_self_nonneg x
  nlinarith [hsq, h1, h2]

/-- Cauchy–Schwarz for the quadratic form: the perturbation of a quadratic form by
`Δ` is controlled by the Euclidean norm of `Δ`. -/
theorem abs_quad_le (Δ : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    |x ⬝ᵥ (Δ *ᵥ x)| ≤ ‖toE Δ‖ * (x ⬝ᵥ x) := by
  rw [quad_eq_inner, ← norm_toE_vecMulVec x]
  exact abs_real_inner_le_norm _ _

/-! ### Uniform positivity of a positive definite quadratic form -/

theorem norm_toLp (x : Fin nn → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin nn))‖ = Real.sqrt (x ⬝ᵥ x) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, sq_abs, pow_two]

theorem quad_smul (M : Matrix (Fin nn) (Fin nn) ℝ) (t : ℝ) (x : Fin nn → ℝ) :
    (t • x) ⬝ᵥ (M *ᵥ (t • x)) = t ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
  rw [quad_eq_sum, quad_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

theorem dot_smul_self (t : ℝ) (x : Fin nn → ℝ) : (t • x) ⬝ᵥ (t • x) = t ^ 2 * (x ⬝ᵥ x) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A positive definite quadratic form dominates a positive multiple of `‖x‖²`.
This is the compactness step: the form attains a positive minimum on the unit sphere. -/
theorem exists_pos_lower (M : Matrix (Fin nn) (Fin nn) ℝ)
    (hM : ∀ x : Fin nn → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin nn → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by
  classical
  rcases Nat.eq_zero_or_pos nn with h0 | hpos
  · subst h0
    exact ⟨1, one_pos, fun x => by simp [dotProduct]⟩
  · set φ : EuclideanSpace ℝ (Fin nn) → ℝ :=
      fun u => (WithLp.ofLp u) ⬝ᵥ (M *ᵥ (WithLp.ofLp u)) with hφdef
    have hcont : Continuous φ := by
      have hrw : φ = fun u : EuclideanSpace ℝ (Fin nn) => ∑ i, ∑ j, M i j * (u i * u j) := by
        funext u; rw [hφdef]; exact quad_eq_sum M _
      rw [hrw]
      refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
      exact continuous_const.mul
        ((PiLp.continuous_apply 2 (fun _ : Fin nn => ℝ) i).mul
          (PiLp.continuous_apply 2 (fun _ : Fin nn => ℝ) j))
    have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin nn)) 1).Nonempty := by
      refine ⟨EuclideanSpace.single ⟨0, hpos⟩ 1, ?_⟩
      simp
    obtain ⟨u₀, hu₀mem, hu₀min⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin nn)) 1).exists_isMinOn hne hcont.continuousOn
    have hu₀norm : ‖u₀‖ = 1 := mem_sphere_zero_iff_norm.mp hu₀mem
    have hu₀ne : (WithLp.ofLp u₀ : Fin nn → ℝ) ≠ 0 := by
      intro hz
      have : u₀ = 0 := by ext i; exact congrFun hz i
      rw [this] at hu₀norm; simp at hu₀norm
    refine ⟨φ u₀, hM _ hu₀ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [dotProduct]
    · have hxx : 0 < x ⬝ᵥ x := dotProduct_self_pos hx
      set r : ℝ := Real.sqrt (x ⬝ᵥ x) with hrdef
      have hrpos : 0 < r := Real.sqrt_pos.mpr hxx
      have hr2 : r ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hxx.le
      set u : EuclideanSpace ℝ (Fin nn) := WithLp.toLp 2 (r⁻¹ • x) with hudef
      have hunorm : ‖u‖ = 1 := by
        rw [hudef, norm_toLp, dot_smul_self, ← hr2]
        rw [show (r⁻¹) ^ 2 * r ^ 2 = 1 by field_simp]
        exact Real.sqrt_one
      have hmem : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin nn)) 1 :=
        mem_sphere_zero_iff_norm.mpr hunorm
      have hkey : φ u₀ ≤ φ u := hu₀min hmem
      have hφu : φ u = (r⁻¹) ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
        rw [hφdef]
        exact quad_smul M (r⁻¹) x
      rw [hφu] at hkey
      have hrne : r ≠ 0 := ne_of_gt hrpos
      have hmul : φ u₀ * r ^ 2 ≤ (r⁻¹ ^ 2 * (x ⬝ᵥ (M *ᵥ x))) * r ^ 2 :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
      have hsimp : (r⁻¹ ^ 2 * (x ⬝ᵥ (M *ᵥ x))) * r ^ 2 = x ⬝ᵥ (M *ᵥ x) := by
        field_simp
      rw [hsimp, hr2] at hmul
      exact hmul

/-! ### Elementary algebra of quadratic forms -/

theorem quad_add (M N : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ ((M + N) *ᵥ x) = x ⬝ᵥ (M *ᵥ x) + x ⬝ᵥ (N *ᵥ x) := by
  rw [Matrix.add_mulVec, dotProduct_add]

theorem quad_neg (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ ((-M) *ᵥ x) = -(x ⬝ᵥ (M *ᵥ x)) := by
  rw [Matrix.neg_mulVec, dotProduct_neg]

theorem quad_smul_mat (c : ℝ) (M : Matrix (Fin nn) (Fin nn) ℝ) (x : Fin nn → ℝ) :
    x ⬝ᵥ ((c • M) *ᵥ x) = c * (x ⬝ᵥ (M *ᵥ x)) := by
  rw [quad_eq_sum, quad_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [Matrix.smul_apply]; ring

theorem quad_one (x : Fin nn → ℝ) : x ⬝ᵥ ((1 : Matrix (Fin nn) (Fin nn) ℝ) *ᵥ x) = x ⬝ᵥ x := by
  rw [Matrix.one_mulVec]

theorem quad_vecMulVec (v x : Fin nn → ℝ) :
    x ⬝ᵥ (Matrix.vecMulVec v v *ᵥ x) = (v ⬝ᵥ x) ^ 2 := by
  rw [quad_eq_sum]
  calc ∑ i, ∑ j, Matrix.vecMulVec v v i j * (x i * x j)
      = ∑ i, ∑ j, (v i * x i) * (v j * x j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          simp [Matrix.vecMulVec_apply]; ring
    _ = (∑ i, v i * x i) * (∑ j, v j * x j) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = (v ⬝ᵥ x) ^ 2 := by rw [dotProduct]; ring

theorem isHermitian_of_isSymm {M : Matrix (Fin nn) (Fin nn) ℝ} (h : M.IsSymm) :
    M.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact isSymm_apply h i j

/-! ### Trace positivity -/

theorem trace_mul_sq (P S : Matrix (Fin nn) (Fin nn) ℝ) (hS : S.IsSymm) :
    (P * (S * S)).trace = ∑ k, (fun i => S k i) ⬝ᵥ (P *ᵥ (fun i => S k i)) := by
  have hSS : (S * S).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, hS.eq]
  rw [trace_mul_eq_sum P (S * S) hSS]
  have hz : ∀ i j, (S * S) i j = ∑ k, S k i * S k j := by
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [isSymm_apply hS i k]
  calc ∑ i, ∑ j, P i j * (S * S) i j
      = ∑ i, ∑ j, ∑ k, P i j * (S k i * S k j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hz i j, Finset.mul_sum]
    _ = ∑ i, ∑ k, ∑ j, P i j * (S k i * S k j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, P i j * (S k i * S k j) := Finset.sum_comm
    _ = ∑ k, (fun i => S k i) ⬝ᵥ (P *ᵥ (fun i => S k i)) :=
        Finset.sum_congr rfl fun k _ => (quad_eq_sum P (fun i => S k i)).symm

/-- `tr(PZ) > 0` for `P` positive definite and `Z` positive semidefinite and nonzero. -/
theorem trace_mul_pos (P Z : Matrix (Fin nn) (Fin nn) ℝ) (hP : P.PosDef)
    (hZ : Z.PosSemidef) (hZne : Z ≠ 0) : 0 < (P * Z).trace := by
  classical
  obtain ⟨c, hc, hlow⟩ := exists_pos_lower P (fun x hx => by
    simpa using hP.dotProduct_mulVec_pos hx)
  have hSpsd : (CFC.sqrt Z).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Z)
  have hSsq : CFC.sqrt Z * CFC.sqrt Z = Z := by
    have h := CFC.sq_sqrt Z (Matrix.nonneg_iff_posSemidef.mpr hZ)
    rwa [sq] at h
  set S : Matrix (Fin nn) (Fin nn) ℝ := CFC.sqrt Z with hSdef
  have hSsymm : S.IsSymm := hSpsd.isHermitian
  have hSne : S ≠ 0 := by
    intro h; apply hZne; rw [← hSsq, h, Matrix.zero_mul]
  obtain ⟨k0, i0, hk0⟩ : ∃ k i, S k i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hSne (by ext k i; simp [hcon k i])
  rw [← hSsq, trace_mul_sq P S hSsymm]
  refine lt_of_lt_of_le ?_ (Finset.sum_le_sum fun k _ => hlow (fun i => S k i))
  refine Finset.sum_pos' (fun k _ => mul_nonneg hc.le (dotProduct_self_nonneg _))
    ⟨k0, Finset.mem_univ k0, ?_⟩
  exact mul_pos hc (dotProduct_self_pos (fun h => hk0 (congrFun h i0)))



/-! ### The cone of positive semidefinite matrices, as a cone in `ℝ^(nn·nn)` -/

/-- Matrices with nonnegative quadratic form. On symmetric matrices this is exactly
the positive semidefinite cone; the extra (non-symmetric) directions are what gives
it a nonempty interior inside the full matrix space. -/
def Kcone (nn : ℕ) : Set (EuclideanSpace ℝ (Fin (nn * nn))) :=
  {y | ∀ x : Fin nn → ℝ, 0 ≤ x ⬝ᵥ ((ofE y) *ᵥ x)}

/-- Matrices with positive definite quadratic form. -/
def PDset (nn : ℕ) : Set (EuclideanSpace ℝ (Fin (nn * nn))) :=
  {y | ∀ x : Fin nn → ℝ, x ≠ 0 → 0 < x ⬝ᵥ ((ofE y) *ᵥ x)}

theorem convex_Kcone : Convex ℝ (Kcone nn) := by
  rintro y₁ h₁ y₂ h₂ a b ha hb hab x
  have hof : ofE (a • y₁ + b • y₂) = a • ofE y₁ + b • ofE y₂ := rfl
  rw [hof, quad_add, quad_smul_mat, quad_smul_mat]
  exact add_nonneg (mul_nonneg ha (h₁ x)) (mul_nonneg hb (h₂ x))

theorem smul_mem_Kcone {t : ℝ} (ht : 0 < t) {y : EuclideanSpace ℝ (Fin (nn * nn))}
    (hy : y ∈ Kcone nn) : t • y ∈ Kcone nn := by
  intro x
  have hof : ofE (t • y) = t • ofE y := rfl
  rw [hof, quad_smul_mat]
  exact mul_nonneg ht.le (hy x)

theorem isClosed_Kcone : IsClosed (Kcone nn) := by
  have hrw : Kcone nn
      = ⋂ x : Fin nn → ℝ, {y : EuclideanSpace ℝ (Fin (nn * nn)) |
          0 ≤ (inner ℝ y (toE (Matrix.vecMulVec x x)) : ℝ)} := by
    ext y
    simp only [Kcone, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h x
      have := h x
      rwa [quad_eq_inner, toE_ofE] at this
    · intro h x
      have := h x
      rwa [quad_eq_inner, toE_ofE]
  rw [hrw]
  exact isClosed_iInter fun x =>
    isClosed_le continuous_const (continuous_id.inner continuous_const)

theorem isOpen_PDset : IsOpen (PDset nn) := by
  rw [Metric.isOpen_iff]
  intro y hy
  obtain ⟨c, hc, hclow⟩ := exists_pos_lower (ofE y) (fun x hx => hy x hx)
  refine ⟨c, hc, fun z hz x hx => ?_⟩
  have hzy : ‖z - y‖ < c := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
  have hxx : 0 < x ⬝ᵥ x := dotProduct_self_pos hx
  have hdecomp : ofE y + (ofE z - ofE y) = ofE z := by abel
  have hsplit : x ⬝ᵥ ((ofE z) *ᵥ x)
      = x ⬝ᵥ ((ofE y) *ᵥ x) + x ⬝ᵥ ((ofE z - ofE y) *ᵥ x) := by
    rw [← quad_add, hdecomp]
  have hbound : |x ⬝ᵥ ((ofE z - ofE y) *ᵥ x)| ≤ ‖z - y‖ * (x ⬝ᵥ x) := by
    have h := abs_quad_le (ofE z - ofE y) x
    rwa [toE_sub, toE_ofE, toE_ofE] at h
  have h1 : -(‖z - y‖ * (x ⬝ᵥ x)) ≤ x ⬝ᵥ ((ofE z - ofE y) *ᵥ x) :=
    neg_le_of_abs_le hbound
  have h2 : ‖z - y‖ * (x ⬝ᵥ x) < c * (x ⬝ᵥ x) := mul_lt_mul_of_pos_right hzy hxx
  have h3 := hclow x
  rw [hsplit]
  linarith

theorem PDset_subset_Kcone : PDset nn ⊆ Kcone nn := by
  intro y hy x
  by_cases hx : x = 0
  · subst hx; simp [dotProduct, Matrix.mulVec]
  · exact (hy x hx).le

/-- On symmetric matrices, membership in `Kcone` is positive semidefiniteness. -/
theorem mem_Kcone_iff {M : Matrix (Fin nn) (Fin nn) ℝ} (hM : M.IsSymm) :
    toE M ∈ Kcone nn ↔ M.PosSemidef := by
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_isSymm hM) fun x => ?_
    rw [show (star x : Fin nn → ℝ) = x from star_trivial x]
    have := h x
    rwa [ofE_toE] at this
  · intro h x
    rw [ofE_toE]
    have := h.dotProduct_mulVec_nonneg x
    rwa [show (star x : Fin nn → ℝ) = x from star_trivial x] at this

theorem zero_mem_Kcone : (0 : EuclideanSpace ℝ (Fin (nn * nn))) ∈ Kcone nn := by
  intro x
  have h : ofE (0 : EuclideanSpace ℝ (Fin (nn * nn))) = 0 := rfl
  rw [h]
  simp [Matrix.zero_mulVec, dotProduct]

/-- An affine function of `x` has a finite infimum over `ℝⁿ` only if its linear part
vanishes, in which case the infimum is its constant term. -/
theorem iInf_affine_eq {n : ℕ} (A : ℝ) (g : Fin n → ℝ) (s : ℝ)
    (h : (⨅ u : EuclideanSpace ℝ (Fin n),
      ((A + ∑ i, (WithLp.ofLp u) i * g i : ℝ) : EReal)) = ((s : ℝ) : EReal)) :
    (∀ i, g i = 0) ∧ A = s := by
  classical
  have hall : ∀ i, g i = 0 := by
    intro i
    by_contra hgi
    have hle : (⨅ u : EuclideanSpace ℝ (Fin n),
        ((A + ∑ i, (WithLp.ofLp u) i * g i : ℝ) : EReal)) ≤ ((s - 1 : ℝ) : EReal) := by
      refine le_trans
        (iInf_le _ (WithLp.toLp 2 (fun k : Fin n => if k = i then (s - 1 - A) / g i else 0))) ?_
      have hsum : ∑ k, (WithLp.ofLp (WithLp.toLp 2
          (fun k : Fin n => if k = i then (s - 1 - A) / g i else 0) :
            EuclideanSpace ℝ (Fin n))) k * g k = s - 1 - A := by
        rw [Finset.sum_eq_single i]
        · show (if i = i then (s - 1 - A) / g i else 0) * g i = s - 1 - A
          rw [if_pos rfl, div_mul_cancel₀ _ hgi]
        · intro k _ hk
          show (if k = i then (s - 1 - A) / g i else 0) * g k = 0
          rw [if_neg hk, zero_mul]
        · intro hcon; exact absurd (Finset.mem_univ i) hcon
      rw [hsum]
      norm_num
    rw [h, EReal.coe_le_coe_iff] at hle
    linarith
  refine ⟨hall, ?_⟩
  have hconst : ∀ u : EuclideanSpace ℝ (Fin n),
      ((A + ∑ i, (WithLp.ofLp u) i * g i : ℝ) : EReal) = ((A : ℝ) : EReal) := by
    intro u
    have hz : ∑ i, (WithLp.ofLp u) i * g i = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hall i, mul_zero]
    rw [hz, add_zero]
  rw [iInf_congr hconst, iInf_const] at h
  exact EReal.coe_eq_coe_iff.mp h

end SDPAux

open ConvexOptimization SDPAux in
theorem solution {n nn : ℕ} (c : Fin n → ℝ)
    (F : Fin n → Matrix (Fin nn) (Fin nn) ℝ) (hF : ∀ i, (F i).IsSymm)
    (G : Matrix (Fin nn) (Fin nn) ℝ) (hG : G.IsSymm)
    (xs : Fin n → ℝ) (hxs : (-(G + ∑ i, xs i • F i)).PosDef)
    (hbdd : BddBelow ((fun x : Fin n → ℝ => c ⬝ᵥ x) ''
      {x | (-(G + ∑ i, x i • F i)).PosSemidef})) :
    ∃ Z : Matrix (Fin nn) (Fin nn) ℝ, Z.PosSemidef ∧
      (∀ i, ((F i) * Z).trace + c i = 0) ∧
      (G * Z).trace =
        sInf ((fun x : Fin n → ℝ => c ⬝ᵥ x) ''
          {x | (-(G + ∑ i, x i • F i)).PosSemidef}) := by
  classical
  -- Entrywise description of the affine matrix family.
  have hFsum : ∀ (y : Fin n → ℝ) (i j : Fin nn),
      (∑ k, y k • F k) i j = ∑ k, y k * F k i j := by
    intro y i j
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun k _ => rfl
  have hAapply : ∀ (y : Fin n → ℝ) (i j : Fin nn),
      (G + ∑ k, y k • F k) i j = G i j + ∑ k, y k * F k i j := by
    intro y i j; rw [Matrix.add_apply, hFsum]
  have hAsymm : ∀ y : Fin n → ℝ, (G + ∑ k, y k • F k).IsSymm := by
    intro y
    refine isSymm_of_apply fun i j => ?_
    rw [hAapply, hAapply, isSymm_apply hG i j]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [isSymm_apply (hF k) i j]
  have hnegsymm : ∀ y : Fin n → ℝ, (-(G + ∑ k, y k • F k)).IsSymm := by
    intro y
    refine isSymm_of_apply fun i j => ?_
    simp only [Matrix.neg_apply]
    rw [isSymm_apply (hAsymm y) i j]
  -- The cone program data.
  set f₀ : EuclideanSpace ℝ (Fin n) → ℝ := fun u => c ⬝ᵥ (WithLp.ofLp u) with hf₀def
  set fm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (nn * nn)) :=
    fun u => toE (G + ∑ i, (WithLp.ofLp u) i • F i) with hfmdef
  have hfeas : ∀ u : EuclideanSpace ℝ (Fin n),
      -fm u ∈ Kcone nn ↔ (-(G + ∑ i, (WithLp.ofLp u) i • F i)).PosSemidef := by
    intro u
    rw [hfmdef]
    simp only
    rw [← toE_neg]
    exact mem_Kcone_iff (hnegsymm _)
  have hset : f₀ '' {u : EuclideanSpace ℝ (Fin n) |
        -fm u ∈ Kcone nn ∧ ∀ j : Fin 0, ⟪(Fin.elim0 j : EuclideanSpace ℝ (Fin n)), u⟫
          = (Fin.elim0 j : ℝ)}
      = (fun x : Fin n → ℝ => c ⬝ᵥ x) '' {x | (-(G + ∑ i, x i • F i)).PosSemidef} := by
    ext r
    constructor
    · rintro ⟨u, ⟨hu, -⟩, rfl⟩
      exact ⟨WithLp.ofLp u, (hfeas u).mp hu, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨WithLp.toLp 2 x, ⟨(hfeas (WithLp.toLp 2 x)).mpr hx, fun j => Fin.elim0 j⟩, rfl⟩
  -- Slater point.
  have hslater : -fm (WithLp.toLp 2 xs) ∈ interior (Kcone nn) := by
    refine interior_maximal PDset_subset_Kcone isOpen_PDset ?_
    intro x hx
    have h1 : (-fm (WithLp.toLp 2 xs)) = toE (-(G + ∑ i, xs i • F i)) := by
      rw [hfmdef, ← toE_neg]
    rw [h1, ofE_toE]
    have := hxs.dotProduct_mulVec_pos hx
    rwa [show (star x : Fin nn → ℝ) = x from star_trivial x] at this
  -- Apply cone-program strong duality.
  obtain ⟨z, nu, hz, hdual⟩ :=
    ConvexOptimization.conic_slater_strong_duality (n := n) (d := nn * nn) (p := 0)
      f₀ (by
        refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
        have hlin : f₀ (a • x + b • y) = a * f₀ x + b * f₀ y := by
          simp only [hf₀def, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by
            simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
              smul_eq_mul]
            ring
        rw [hlin]; simp)
      (Kcone nn) convex_Kcone isClosed_Kcone (fun t ht y hy => smul_mem_Kcone ht hy)
      fm (by
        intro x y θ hθ0 hθ1
        have hmat : θ • (G + ∑ i, (WithLp.ofLp x) i • F i)
            + (1 - θ) • (G + ∑ i, (WithLp.ofLp y) i • F i)
            - (G + ∑ i, (WithLp.ofLp (θ • x + (1 - θ) • y)) i • F i) = 0 := by
          ext i j
          rw [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
            smul_eq_mul, smul_eq_mul, hAapply, hAapply, hAapply, Matrix.zero_apply]
          have hterm : ∀ k : Fin n, (WithLp.ofLp (θ • x + (1 - θ) • y)) k * F k i j
              = θ * ((WithLp.ofLp x) k * F k i j)
                + (1 - θ) * ((WithLp.ofLp y) k * F k i j) := by
            intro k
            simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
              smul_eq_mul]
            ring
          rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
          ring
        have hzero : θ • fm x + (1 - θ) • fm y - fm (θ • x + (1 - θ) • y) = 0 := by
          rw [hfmdef]
          simp only
          rw [← toE_smul, ← toE_smul, ← toE_add, ← toE_sub, hmat]
          ext k; rfl
        rw [hzero]
        exact zero_mem_Kcone)
      Fin.elim0 (linearIndependent_empty_type) Fin.elim0
      (WithLp.toLp 2 xs) hslater (fun j => Fin.elim0 j)
      (by rw [hset]; exact hbdd)
  -- Read off the certificate.
  set W : Matrix (Fin nn) (Fin nn) ℝ := ofE z with hWdef
  set Z : Matrix (Fin nn) (Fin nn) ℝ := (2 : ℝ)⁻¹ • (W + Wᵀ) with hZdef
  have hZsymm : Z.IsSymm := by
    unfold Matrix.IsSymm
    rw [hZdef, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose,
      add_comm Wᵀ W]
  have hWE : toE W = z := by rw [hWdef, toE_ofE]
  have hpair : ∀ M : Matrix (Fin nn) (Fin nn) ℝ, M.IsSymm →
      (inner ℝ z (toE M) : ℝ) = (M * Z).trace := by
    intro M hM
    have hzM : (inner ℝ z (toE M) : ℝ) = ∑ i, ∑ j, W i j * M i j := by
      rw [← hWE, inner_toE]
    have hswap : ∑ i, ∑ j, W j i * M i j = ∑ i, ∑ j, W i j * M i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [isSymm_apply hM i j]
    have hZij : ∀ i j, M i j * Z i j = (W i j * M i j + W j i * M i j) / 2 := by
      intro i j
      simp only [hZdef, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
      ring
    have hinner : ∀ i : Fin nn, ∑ j, (W i j * M i j + W j i * M i j) / 2
        = ((∑ j, W i j * M i j) + (∑ j, W j i * M i j)) / 2 := by
      intro i; rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [hzM, trace_mul_eq_sum M Z hZsymm,
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hZij i j,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i,
      ← Finset.sum_div, Finset.sum_add_distrib, hswap]
    ring
  have hZpsd : Z.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_isSymm hZsymm) ?_
    intro v
    rw [show (star v : Fin nn → ℝ) = v from star_trivial v]
    have hq : v ⬝ᵥ (Z *ᵥ v) = (Matrix.vecMulVec v v * Z).trace := by
      rw [trace_mul_eq_sum _ Z hZsymm, quad_eq_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        simp [Matrix.vecMulVec_apply]; ring
    rw [hq, ← hpair _ (vecMulVec_isSymm v)]
    have hmem : toE (Matrix.vecMulVec v v) ∈ Kcone nn := by
      intro x; rw [ofE_toE, quad_vecMulVec]; positivity
    have := hz _ hmem
    rwa [real_inner_comm] at this
  -- The Lagrangian is affine in `x`, so finiteness of its infimum forces stationarity.
  set A : ℝ := (G * Z).trace with hAdef
  set g : Fin n → ℝ := fun i => c i + (F i * Z).trace with hgdef
  have hlag : ∀ u : EuclideanSpace ℝ (Fin n),
      f₀ u + (inner ℝ z (fm u) : ℝ) + ∑ j : Fin 0, nu j * (⟪(Fin.elim0 j : EuclideanSpace ℝ (Fin n)), u⟫ - (Fin.elim0 j : ℝ))
        = A + ∑ i, (WithLp.ofLp u) i * g i := by
    intro u
    have hexp : (inner ℝ z (fm u) : ℝ) = A + ∑ i, (WithLp.ofLp u) i * ((F i * Z).trace) := by
      rw [hfmdef]
      simp only
      rw [hpair _ (hAsymm _), Matrix.add_mul, Matrix.trace_add, Finset.sum_mul, Matrix.trace_sum,
        ← hAdef]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [hexp, hf₀def]
    simp only [Finset.sum_empty, Finset.univ_eq_empty, add_zero, hgdef, dotProduct]
    have hR : ∑ i, (WithLp.ofLp u) i * (c i + (F i * Z).trace)
        = ∑ i, c i * (WithLp.ofLp u) i + ∑ i, (WithLp.ofLp u) i * (F i * Z).trace := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hR]
    ring
  have hdual2 : (⨅ u : EuclideanSpace ℝ (Fin n),
      ((A + ∑ i, (WithLp.ofLp u) i * g i : ℝ) : EReal))
      = ((sInf (f₀ '' {u : EuclideanSpace ℝ (Fin n) | -fm u ∈ Kcone nn ∧
          ∀ j : Fin 0, ⟪(Fin.elim0 j : EuclideanSpace ℝ (Fin n)), u⟫
            = (Fin.elim0 j : ℝ)}) : ℝ) : EReal) := by
    rw [← hdual]
    exact iInf_congr fun u => by rw [hlag u]
  obtain ⟨hg0, hA⟩ := iInf_affine_eq A g _ hdual2
  rw [hset] at hA
  refine ⟨Z, hZpsd, fun i => ?_, ?_⟩
  · have hi := hg0 i
    rw [hgdef] at hi
    simp only at hi
    linarith
  · rw [hAdef] at hA
    exact hA
