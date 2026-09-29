-- Prove2me | Definitions.Def_Cryptography_HilbertSpace_VectorStoneWeierstrass
-- name    : Cryptography_HilbertSpace_VectorStoneWeierstrass
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:14:14.613447+00:00
-- url     : https://prove2.me/theorems/b26efa13-4bcf-447c-b437-c76dc2ab0e07
-- title:
--   Aether Catalog definitions — Cryptography_HilbertSpace_VectorStoneWeierstrass
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.HilbertSpace.VectorStoneWeierstrass`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/HilbertSpace/VectorStoneWeierstrass.lean by skeleton subtraction
import Mathlib

/-
# Vector-Valued EML Stone–Weierstrass Theorem

This file lifts the scalar Stone–Weierstrass density theorem from `C(X, ℝ)` to
finite-dimensional vector-valued codomains `C(X, Fin m → ℝ)`.

## Main definitions

* `coordMap i` — the `i`-th coordinate projection as a continuous map
* `VecClass A m` — the coordinatewise vector class attached to a scalar class `A`
* `CoupledVecClass A m` — shared-feature class with continuous output coupling

## Main results

* `closure_vecClass_eq_univ_of_scalar` — if `A` is dense in `C(X, ℝ)`, then
  `VecClass A m` is dense in `C(X, Fin m → ℝ)`
* `exists_mem_vecClass_uniformApprox` — ε-approximation form
* `dense_coupledVecClass_of_dense_scalar` — density of the coupled class
* `comp_mem_coupledVecClass` — closure under continuous output postcomposition
* `dense_into_compactRange_of_retraction` — density with retraction onto compact target
* `softmaxMap_mem_stdSimplex` — softmax maps into the standard simplex
* `eml_vec_stoneWeierstrass` — EML specialization

## Mathematical significance

This development upgrades scalar EML universality into a genuinely usable
vector-valued approximation theory, providing the formal bridge from scalar
universality to multiclass classifiers, controllers, and constrained outputs.
-/

noncomputable section

open ContinuousMap Set Topology Real

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## Core Definitions -/

/-- The `i`-th coordinate projection as a continuous map `C(Fin m → ℝ, ℝ)`. -/
def coordMap (m : ℕ) (i : Fin m) : C(Fin m → ℝ, ℝ) :=
  ⟨fun x => x i, continuous_apply i⟩

/-- The coordinatewise vector class: `F ∈ VecClass A m` iff every coordinate
    projection `(coordMap m i).comp F` belongs to the scalar class `A`. -/
def VecClass (A : Set C(X, ℝ)) (m : ℕ) : Set C(X, Fin m → ℝ) :=
  {F | ∀ i : Fin m, (coordMap m i).comp F ∈ A}


/-- Assemble a vector-valued continuous map from coordinate functions. -/
def assembleVec {m : ℕ} (g : Fin m → C(X, ℝ)) : C(X, Fin m → ℝ) :=
  ⟨fun x i => g i x, continuous_pi (fun i => (g i).continuous)⟩




/-! ## Coordinatewise Norm Estimates -/

/-
Pointwise bound: if every coordinate is bounded by `δ`, then the pi-norm
    (which is the sup norm on `Fin m → ℝ`) is bounded by `δ`.
-/


/-! ## Main Density Theorem -/

/-
**Coordinatewise density in `C(X, Fin m → ℝ)`.**
    If the scalar class `A` is dense in `C(X, ℝ)`, then every vector-valued
    function is in the closure of `VecClass A m`.
-/

/-
**ε-approximation form.**
-/


/-! ## Coupled Vector Class -/

/-- The coupled-output class: vector maps obtained by applying a continuous
    readout to finitely many shared scalar features from `A`. -/
def CoupledVecClass (A : Set C(X, ℝ)) (m : ℕ) : Set C(X, Fin m → ℝ) :=
  {F | ∃ k : ℕ, ∃ g : Fin k → C(X, ℝ),
      (∀ j, g j ∈ A) ∧
      ∃ φ : C(Fin k → ℝ, Fin m → ℝ),
        F = φ.comp ⟨fun x j => g j x, continuous_pi (fun j => (g j).continuous)⟩}

/-
`VecClass A m ⊆ CoupledVecClass A m`: use identity readout with `k = m`.
-/


/-
Closure under continuous output postcomposition.
-/

/-! ## Retraction onto Compact Targets -/

/-
Density into a compact target `K` via a continuous retraction `r`.
    If `r` fixes `K` pointwise and maps everything into `K`, and `F` maps into `K`,
    then `F` can be approximated by coupled-class maps that also map into `K`.
-/

/-! ## Simplex and Softmax -/

/-- The softmax map sends any vector to the probability simplex `stdSimplex ℝ (Fin m)`.
    Requires `m > 0` so that the denominator is positive. -/
def softmaxMap (m : ℕ) (hm : 0 < m) : C(Fin m → ℝ, Fin m → ℝ) :=
  ⟨fun y i => exp (y i) / ∑ j, exp (y j), by
    apply continuous_pi; intro i
    apply Continuous.div
    · exact (continuous_apply i).rexp
    · exact continuous_finset_sum _ (fun j _ => (continuous_apply j).rexp)
    · intro y
      apply ne_of_gt
      apply Finset.sum_pos (fun j _ => exp_pos _)
      rw [Finset.univ_nonempty_iff]; exact ⟨⟨0, hm⟩⟩⟩

/-
Softmax output lies in the standard simplex.
-/

/-
Interior-simplex density: strictly positive simplex-valued maps can be
    approximated by softmax-composed coupled-class maps.
-/

/-! ## EML Specialization -/

section EMLSpecialization

variable {n : ℕ} (Φ : Fin n → C(X, ℝ))

/-- The logistic (sigmoid) activation function. -/
private def logistic' (x : ℝ) : ℝ := 1 / (1 + exp (-x))

private lemma logistic'_continuous : Continuous logistic' := by
  unfold logistic'
  apply Continuous.div continuous_const
  · exact continuous_const.add continuous_neg.rexp
  · intro x; positivity

/-- EML exponential generator: `exp(∑ᵢ wᵢ Φᵢ(x) + b)`. -/
private def emlExpGen' (w : Fin n → ℝ) (b : ℝ) : C(X, ℝ) :=
  ⟨fun x => exp (∑ i, w i * Φ i x + b),
    (continuous_finset_sum _ (fun i _ => continuous_const.mul (Φ i).continuous) |>.add
      continuous_const).rexp⟩

/-- EML logistic generator: `σ(∑ᵢ wᵢ Φᵢ(x) + b)`. -/
private def emlLogisticGen' (w : Fin n → ℝ) (b : ℝ) : C(X, ℝ) :=
  ⟨fun x => logistic' (∑ i, w i * Φ i x + b),
    logistic'_continuous.comp
      (continuous_finset_sum _ (fun i _ => continuous_const.mul (Φ i).continuous) |>.add
        continuous_const)⟩

/-- The set of all EML generators (exponential and logistic). -/
private def emlGenerators' : Set C(X, ℝ) :=
  {f | ∃ w b, f = emlExpGen' Φ w b} ∪ {f | ∃ w b, f = emlLogisticGen' Φ w b}

/-- The ℝ-subalgebra of C(X, ℝ) generated by the EML generators. -/
def emlSubalgebra' : Subalgebra ℝ C(X, ℝ) :=
  Algebra.adjoin ℝ (emlGenerators' Φ)

/-- The EML scalar class: the carrier set of the EML subalgebra. -/
def EMLScalarClass : Set C(X, ℝ) := ↑(emlSubalgebra' Φ)





end EMLSpecialization

end


