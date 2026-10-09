-- Prove2me | Definitions.Def_Nonadditivity_FiniteMomentMatching
-- name    : Nonadditivity_FiniteMomentMatching
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:45:08.355284+00:00
-- url     : https://prove2.me/theorems/4b574e98-524a-4fa1-9782-b28a804420bb
-- title:
--   Exact transfer from regular norms to finite trace moments
-- statement:
--   Let $G$ be a group, $f\in\mathbb C[G]$ a finitely supported group polynomial, $\lambda(f)$ its left-regular operator on $\ell^2(G)$, and $\rho:G\to M_d(\mathbb C)$ a matrix representation. Write $\rho(f)$ for algebraic evaluation. If $\operatorname{Tr}\rho(g)=d\,\mathbf1_{g=1}$ for every group element in the support of $f^q$, then
--   $$\operatorname{Tr}(\rho(f)^q)=d\,(f^q)(1),\qquad \operatorname{Re}\operatorname{Tr}(\rho(f)^q)\le d\|\lambda(f)\|^q.$$
--   Here $q\ge0$ is an integer. For the block-adjoint polynomial $\gamma_A=K^{-n}\sum_{a,b}A_{ab}\,\delta_{w_a^{-1}w_b}$ on a product of free groups, every coordinate word in $\gamma_A^q$ has length at most $2q$. The proved free norm estimate therefore bounds finite moments by $d(c_{K,n}\|A\|_{\rm HS})^q$ for traceless $A$, $K\ge2$, $n\ge1$, where $c_{K,n}=\sqrt{((1+9/K)^n-1)/K^n}$.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/FiniteMomentMatching.lean#L29-L219

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_CollinsYoun
import Definitions.Def_Nonadditivity_CollinsYounProduct
import Definitions.Def_Nonadditivity_CollinsYounTensor
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeCreation
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularFubini
import Definitions.Def_Nonadditivity_RegularRestriction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/







/-! # Exact finite-quotient moments of the free channel polynomial

Finite word separation suffices for trace moments. No strong convergence of
finite operator norms is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Nonadditivity.FiniteMomentMatching

open FreeModel
open scoped BigOperators ENNReal Pointwise Matrix Matrix.Norms.L2Operator

section RegularAlgebra
variable {G : Type*} [Group G] [DecidableEq G]

/-- The actual infinite regular representation as a monoid homomorphism. -/
def regularHom : G →* (Hilbert G →L[ℂ] Hilbert G) where
  toFun := leftRegular
  map_one' := leftRegular_one
  map_mul' g h := leftRegular_mul g h

/-- Algebraic evaluation of a finitely supported group polynomial. -/
def regularEval : MonoidAlgebra ℂ G →ₐ[ℂ] (Hilbert G →L[ℂ] Hilbert G) :=
  MonoidAlgebra.lift ℂ _ G regularHom

/-- Evaluating the regular polynomial at the identity coordinate selects its identity coefficient. -/
theorem regularEval_vacuum (f : MonoidAlgebra ℂ G) :
    (regularEval f (lp.single 2 (1 : G) (1 : ℂ))) 1 = f 1 := by
  simp [regularEval, MonoidAlgebra.lift_apply, Finsupp.sum,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_smul, regularHom, leftRegular_apply,
    lp.single_apply, Pi.single_apply, inv_eq_one]
  intro h
  exact h.symm

/-- The identity coefficient is bounded by the concrete regular operator norm. -/
theorem norm_identity_coefficient_le (f : MonoidAlgebra ℂ G) :
    ‖f 1‖ ≤ ‖regularEval f‖ := by
  let e : Hilbert G := lp.single 2 (1 : G) (1 : ℂ)
  have he : ‖e‖ = 1 := by
    change ‖lp.single (E := fun _ : G => ℂ) (2 : ℝ≥0∞) (1 : G) (1 : ℂ)‖ = 1
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one]
  have hv : (regularEval f e) 1 = f 1 := regularEval_vacuum f
  have hcoord : ‖(regularEval f e) 1‖ ≤ ‖regularEval f e‖ :=
    lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (regularEval f e) 1
  have hop : ‖regularEval f e‖ ≤ ‖regularEval f‖ * ‖e‖ :=
    (regularEval f).le_opNorm e
  rw [hv] at hcoord
  rw [he, mul_one] at hop
  exact hcoord.trans hop

/-- A subadditive word-length bound is preserved by polynomial powers. -/
theorem support_pow_length_le (f : MonoidAlgebra ℂ G) (len : G → ℕ)
    (hone : len 1 = 0) (hmul : ∀ g h, len (g * h) ≤ len g + len h)
    (r : ℕ) (hf : ∀ g ∈ f.support, len g ≤ r) (q : ℕ) :
    ∀ g ∈ (f ^ q).support, len g ≤ q * r := by
  induction q with
  | zero =>
      intro g hg
      have : g = 1 := by simpa using hg
      simp [this, hone]
  | succ q ih =>
      intro g hg
      rw [pow_succ] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_mul _ _ hg)
      exact (hmul a b).trans (by nlinarith [ih a ha, hf b hb])

end RegularAlgebra

section FiniteEvaluation
variable {G ν : Type*} [Group G] [DecidableEq G] [Fintype ν] [DecidableEq ν]

/-- Evaluation at any concrete finite matrix representation. -/
def finiteEval (ρ : G →* Matrix ν ν ℂ) : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix ν ν ℂ :=
  MonoidAlgebra.lift ℂ _ G ρ

/-- Exact trace matching for a representation with the regular character on the support. -/
theorem trace_finiteEval (ρ : G →* Matrix ν ν ℂ) (f : MonoidAlgebra ℂ G)
    (htrace : ∀ g ∈ f.support,
      (ρ g).trace = (Fintype.card ν : ℂ) * (if g = 1 then 1 else 0)) :
    (finiteEval ρ f).trace = (Fintype.card ν : ℂ) * f 1 := by
  rw [finiteEval, MonoidAlgebra.lift_apply]
  change (∑ g ∈ f.support, f g • ρ g).trace = _
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul]
  calc
    (∑ g ∈ f.support, f g * (ρ g).trace) =
        ∑ g ∈ f.support, (Fintype.card ν : ℂ) * (if g = 1 then f g else 0) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [htrace g hg]
      split_ifs <;> simp_all [mul_comm]
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      by_cases h : (1 : G) ∈ f.support
      · simp [h]
      · simp [h, Finsupp.notMem_support_iff.mp h]



/-- Exact finite moment matching implies the regular-norm upper bound. -/
theorem trace_pow_re_le (ρ : G →* Matrix ν ν ℂ) (f : MonoidAlgebra ℂ G) (q : ℕ)
    (htrace : ∀ g ∈ (f ^ q).support,
      (ρ g).trace = (Fintype.card ν : ℂ) * (if g = 1 then 1 else 0)) :
    ((finiteEval ρ f) ^ q).trace.re ≤
      (Fintype.card ν : ℝ) * ‖regularEval f‖ ^ q := by
  rw [← map_pow, trace_finiteEval ρ (f ^ q) htrace, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ((f ^ q) 1).re ≤ ‖(f ^ q) 1‖ := Complex.re_le_norm _
    _ ≤ ‖regularEval (f ^ q)‖ := norm_identity_coefficient_le _
    _ = ‖(regularEval f) ^ q‖ := by rw [map_pow]
    _ ≤ ‖regularEval f‖ ^ q := by
      cases q with
      | zero => exact ContinuousLinearMap.norm_id_le
      | succ q => exact norm_pow_le' _ (Nat.succ_pos q)

end FiniteEvaluation

section ChannelPolynomial

/-- The channel adjoint polynomial, with its coefficients and group words recorded algebraically. -/
def gammaPolynomial {K n : ℕ} (A : Matrix (Branch K n) (Branch K n) ℂ) :
    MonoidAlgebra ℂ (ProductFreeGroup K n) :=
  ∑ a, ∑ b, MonoidAlgebra.single ((branchWord a)⁻¹ * branchWord b)
    ((1 / (K : ℂ)^n) * A a b)

@[simp] theorem regularEval_gammaPolynomial {K n : ℕ}
    (A : Matrix (Branch K n) (Branch K n) ℂ) :
    regularEval (gammaPolynomial A) = gamma A := by
  simp [gammaPolynomial, regularEval, MonoidAlgebra.lift_single, gamma,
    Finset.smul_sum, mul_smul, regularHom]

theorem coefficient_sum {G ι : Type*} (s : Finset ι) (f : ι → MonoidAlgebra ℂ G)
    (g : G) : (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, MonoidAlgebra.coe_add, Pi.add_apply, ih]

/-- Each coordinate of a word occurring in the adjoint has length at most two. -/
theorem branch_pair_length_le {K n : ℕ} (a b : Branch K n) (j : Fin n) :
    FreeGroup.norm (((branchWord a)⁻¹ * branchWord b) j) ≤ 2 := by
  simpa [branchWord, FreeGroup.norm_inv_eq, FreeGroup.norm_of] using
    FreeGroup.norm_mul_le (FreeGroup.of (a j))⁻¹ (FreeGroup.of (b j))

theorem gammaPolynomial_support_length_le {K n : ℕ}
    (A : Matrix (Branch K n) (Branch K n) ℂ)
    (g : ProductFreeGroup K n) (hg : g ∈ (gammaPolynomial A).support) (j : Fin n) :
    FreeGroup.norm (g j) ≤ 2 := by
  by_contra hn
  have hz : gammaPolynomial A g = 0 := by
    simp only [gammaPolynomial, coefficient_sum]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    have hne : (branchWord a)⁻¹ * branchWord b ≠ g := by
      intro h
      exact hn (h ▸ branch_pair_length_le a b j)
    simp [hne]
  exact (Finsupp.mem_support_iff.mp hg) hz

/-- A moment of order `q` only inspects words of coordinate length at most `2q`. -/
theorem gammaPolynomial_pow_support_length_le {K n : ℕ}
    (A : Matrix (Branch K n) (Branch K n) ℂ) (q : ℕ)
    (g : ProductFreeGroup K n) (hg : g ∈ (gammaPolynomial A ^ q).support) (j : Fin n) :
    FreeGroup.norm (g j) ≤ 2*q := by
  have h := support_pow_length_le (gammaPolynomial A) (fun w => FreeGroup.norm (w j))
    (by simp) (fun g h => FreeGroup.norm_mul_le (g j) (h j))
    2 (fun w hw => gammaPolynomial_support_length_le A w hw j) q g hg
  simpa only [Nat.mul_comm] using h

/-- The finite evaluation is literally the normalized adjoint polynomial. -/
theorem finiteEval_gammaPolynomial {K n : ℕ} {ν : Type*} [Fintype ν] [DecidableEq ν]
    (ρ : ProductFreeGroup K n →* Matrix ν ν ℂ)
    (A : Matrix (Branch K n) (Branch K n) ℂ) :
    finiteEval ρ (gammaPolynomial A) =
      (1 / (K : ℂ)^n) • ∑ a, ∑ b, A a b • ρ ((branchWord a)⁻¹ * branchWord b) := by
  simp [finiteEval, gammaPolynomial, MonoidAlgebra.lift_single, Finset.smul_sum, mul_smul]

/-- Exact moment matching transfers the proved free norm bound to a finite trace moment. -/
theorem gamma_trace_pow_re_le {K n : ℕ} {ν : Type*} [Fintype ν] [DecidableEq ν]
    (hK : 2 ≤ K) (hn : 1 ≤ n)
    (ρ : ProductFreeGroup K n →* Matrix ν ν ℂ)
    (A : Matrix (Branch K n) (Branch K n) ℂ) (hA : A.trace = 0) (q : ℕ)
    (htrace : ∀ g : ProductFreeGroup K n, (∀j, FreeGroup.norm (g j) ≤ 2*q) →
      (ρ g).trace = (Fintype.card ν : ℂ) * (if g = 1 then 1 else 0)) :
    ((finiteEval ρ (gammaPolynomial A))^q).trace.re ≤
      (Fintype.card ν : ℝ) * (c K n * AdjointPurity.hsLength A)^q := by
  apply (trace_pow_re_le ρ (gammaPolynomial A) q (fun g hg =>
    htrace g (gammaPolynomial_pow_support_length_le A q g hg))).trans
  rw [regularEval_gammaPolynomial]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (norm_nonneg _) (CollinsYounProduct.collinsYounBound hK hn A hA) q

end ChannelPolynomial

end Nonadditivity.FiniteMomentMatching


