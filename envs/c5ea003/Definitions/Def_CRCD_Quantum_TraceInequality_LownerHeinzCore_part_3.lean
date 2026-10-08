-- Prove2me | Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
-- name    : CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:47:36.96379+00:00
-- url     : https://prove2.me/theorems/0ab38355-aa50-4cdc-81a0-011779eff8cd
-- title:
--   Operator convexity of powers from one to two
-- statement:
--   Let $\mathcal A$ be a nontrivial complex C*-algebra with compatible partial order, star order and the nonnegative-spectrum class. This part completes the power-convexity argument for $1\le p\le2$: for self-adjoint $A,B$ with spectra in $[0,\infty)$ and $0\le\theta\le1$,
--   $$
--   \bigl((1-\theta)A+\theta B\bigr)^p
--    \le(1-\theta)A^p+\theta B^p.
--   $$
--   Powers use real continuous functional calculus, so singular positive operators are allowed. There is no finite-dimensional assumption.
--
--   For interior exponents, the supporting results prove convexity of the operator-valued integral kernel $t^{q-1}x^2/(x+t)$, with $0<q<1$ and $t>0$, and identify its nonunital functional calculus with multiplication by the underlying positive operator. The almost-everywhere identity is stated for an arbitrary real measure restricted to $(0,\infty)$. These interfaces establish convexity of $A\mapsto A^{1+q}$ and hence of all powers with $1<p<2$. The quadratic endpoint is handled by the exact noncommutative algebraic identity
--   $$
--   (1-\theta)A^2+\theta B^2-
--    \bigl((1-\theta)A+\theta B\bigr)^2
--    =\theta(1-\theta)(A-B)^2.
--   $$
--   For self-adjoint $A,B$ and $0\le\theta\le1$, the right-hand side is positive. Several retained scalar-distributivity and multiplication expansions justify this identity; those algebraic identities themselves hold without positivity assumptions and for arbitrary real $\theta$. The final statement includes both endpoints $p=1,2$.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/TraceInequality/LownerHeinzCore.lean#L1336-L1811

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_2

/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/





set_option linter.style.longLine false

namespace LownerHeinzCore

universe u v

open CFC

section Pure

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]



































end Pure

section Spectrum

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]
variable [NonnegSpectrumClass ℝ 𝓐]















-- Reduces to `one_div_operatorConvexOn_Ioi` and is also elaboration-heavy.


























 lemma convexOn_G_rpowIntegrand₀₁_mul {q : NNReal} (hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (htpos : 0 < t) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X) := by
  -- use `EqOn` to replace the integrand by a structured convex expression
  let r : ℝ := t ^ ((q : ℝ) - 1)
  have hr_nonneg : 0 ≤ r :=
    Real.rpow_nonneg (le_of_lt htpos) _
  have hs : Convex ℝ (Set.Ici (0 : 𝓐)) := convex_Ici (𝕜 := ℝ) (0 : 𝓐)
  have h_aff : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ X - algebraMap ℝ (𝓐) t) := by
    have hid : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ X) := by
      simpa using (convexOn_id (𝕜 := ℝ) (s := Set.Ici (0 : 𝓐)) hs)
    have hconst : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun _ : 𝓐 ↦ -algebraMap ℝ (𝓐) t) :=
      convexOn_const (-algebraMap ℝ (𝓐) t) hs
    simpa [sub_eq_add_neg] using hid.add hconst
  have h_one_div : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ cfcR (fun x : ℝ ↦ 1 / (x + t)) X) :=
    _root_.LownerHeinzCore.convexOn_cfcR_one_div_add_t  t htpos
  have h_inner :
      ConvexOn ℝ (Set.Ici (0 : 𝓐))
        (fun X : 𝓐 ↦ X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X) := by
    have hterm :
        ConvexOn ℝ (Set.Ici (0 : 𝓐))
          (fun X : 𝓐 ↦ (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X) :=
      (h_one_div.smul (sq_nonneg t))
    exact h_aff.add hterm
  have h_rhs :
      ConvexOn ℝ (Set.Ici (0 : 𝓐))
        (fun X : 𝓐 ↦ r •
          (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X)) :=
    h_inner.smul hr_nonneg
  -- transfer convexity back to the `cfcₙ` expression
  refine h_rhs.congr ?_
  intro X hX
  have : (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X) X
      =
      (fun X : 𝓐 ↦ r •
        (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X)) X := by
    simpa [r] using _root_.LownerHeinzCore.G_eqOn_rpowIntegrand₀₁_mul  hq_real t htpos hX
  simpa using this.symm

omit [Nontrivial (𝓐)] in
 lemma ae_cfcₙ_mul_id_rpowIntegrand₀₁_restrict_Ioi {q : NNReal} (hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (μ : MeasureTheory.Measure ℝ) (A : 𝓐) (hA0 : 0 ≤ A) :
    ∀ᵐ t ∂(μ.restrict (Set.Ioi (0 : ℝ))),
      cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) A =
        A * cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have hqs : quasispectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := quasispectrum_nonneg_of_nonneg A hA0 x hx
    simpa [Set.Ici] using hx0
  have hg : ContinuousOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (quasispectrum ℝ A) :=
    (Real.continuousOn_rpowIntegrand₀₁_Ici hq_real ht).mono hqs
  have hG_mul :
      cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) A
        =
        cfcₙ (fun x : ℝ ↦ x) A * cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A := by
    simpa using
      (cfcₙ_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := fun x : ℝ ↦ x) (g := Real.rpowIntegrand₀₁ (q : ℝ) t) (a := A)
        (hf := continuousOn_id) (hf0 := by simp) (hg := hg) (hg0 := by simp))
  have hA_id : cfcₙ (fun x : ℝ ↦ x) A = A := by
    simpa using (cfcₙ_id' (R := ℝ) (a := A) (ha := IsSelfAdjoint.of_nonneg hA0))
  simp [hA_id, hG_mul]

 lemma convexOn_nnrpow_Ioo_one_add {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ ((1 : NNReal) + q)) := by
  -- real exponent in `(0,1)`
  have hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · exact (NNReal.coe_pos).2 hq.1
    · exact (NNReal.coe_lt_coe).2 hq.2
  -- integral representation for `a ↦ a ^ q`
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ (A := 𝓐) hq
  let ν : MeasureTheory.Measure ℝ := μ.restrict (Set.Ioi (0 : ℝ))
  let F0 : ℝ → 𝓐 → 𝓐 := fun t A => cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A
  let G : ℝ → 𝓐 → 𝓐 := fun t A =>
    cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) A
  have hF0_int : ∀ A ∈ Set.Ici (0 : 𝓐), MeasureTheory.Integrable (fun t => F0 t A) ν := by
    intro A hA
    simpa [F0, ν, MeasureTheory.IntegrableOn] using (hμ A hA).1
  have hG_int : ∀ A ∈ Set.Ici (0 : 𝓐), MeasureTheory.Integrable (fun t => G t A) ν := by
    intro A hA
    have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
    have hAF : MeasureTheory.Integrable (fun t => A * F0 t A) ν := by
      -- left multiplication by a constant is a continuous linear map
      have hF : MeasureTheory.Integrable (fun t => F0 t A) ν := hF0_int A hA
      simpa [ContinuousLinearMap.mul_apply'] using
        (ContinuousLinearMap.mul ℝ (𝓐) A).integrable_comp hF
    have hG_mul_ae : ∀ᵐ t ∂ν, G t A = A * F0 t A := by
      simpa [ν, G, F0] using
        _root_.LownerHeinzCore.ae_cfcₙ_mul_id_rpowIntegrand₀₁_restrict_Ioi  (q := q) hq_real μ A hA0
    exact hAF.congr (hG_mul_ae.mono fun _ ht => ht.symm)
  have hG_conv :
      ∀ᵐ t ∂ν, ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 => G t A) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hconv :
        ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X) :=
      _root_.LownerHeinzCore.convexOn_G_rpowIntegrand₀₁_mul  hq_real t ht
    simpa [G] using hconv
  have hconv_int :
      ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ ∫ t, G t A ∂ν) :=
    MeasureTheory.integral_convexOn_of_integrand_ae
      (μ := ν) (s := Set.Ici (0 : 𝓐)) (f := fun t A => G t A)
      (convex_Ici (𝕜 := ℝ) (0 : 𝓐)) hG_conv hG_int
  -- identify the integral with `A ^ (1 + q)` on `Ici 0`
  refine hconv_int.congr ?_
  intro A hA
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hq0 : (0 : NNReal) < q := hq.1
  have hpow :
      A ^ ((1 : NNReal) + q) = A * (A ^ q) := by
    have h1 : A ^ ((1 : NNReal) + q) = A ^ (1 : NNReal) * A ^ q := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (CFC.nnrpow_add (A := 𝓐) (a := A) (x := (1 : NNReal)) (y := q) zero_lt_one hq0)
    simpa [CFC.nnrpow_one (A := 𝓐) A hA0] using h1
  have hEq_q : A ^ q = ∫ t, F0 t A ∂ν := by
    simpa [F0, ν] using (hμ A hA).2
  have hEq_mul :
      A * (∫ t, F0 t A ∂ν) = ∫ t, A * F0 t A ∂ν := by
    have h :
        (∫ t, (ContinuousLinearMap.mul ℝ (𝓐) A) (F0 t A) ∂ν)
          =
          (ContinuousLinearMap.mul ℝ (𝓐) A) (∫ t, F0 t A ∂ν) :=
      (ContinuousLinearMap.mul ℝ (𝓐) A).integral_comp_comm (μ := ν) (φ_int := hF0_int A hA)
    exact h.symm
  have hEq :
      A ^ ((1 : NNReal) + q) = ∫ t, G t A ∂ν := by
    calc
      A ^ ((1 : NNReal) + q) = A * (A ^ q) := hpow
      _ = A * (∫ t, F0 t A ∂ν) := by simp [hEq_q]
      _ = ∫ t, A * F0 t A ∂ν := hEq_mul
      _ = ∫ t, G t A ∂ν := by
        have hG_mul_ae : ∀ᵐ t ∂ν, A * F0 t A = G t A := by
          have h' : ∀ᵐ t ∂ν, G t A = A * F0 t A := by
            simpa [ν, G, F0] using
              _root_.LownerHeinzCore.ae_cfcₙ_mul_id_rpowIntegrand₀₁_restrict_Ioi  (q := q) hq_real μ A hA0
          exact h'.mono (fun _ ht => ht.symm)
        simpa using (MeasureTheory.integral_congr_ae hG_mul_ae)
  simp [hEq]

 lemma convexOn_rpow_Ioo_one_two {p : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ p) := by
  -- reduce to the `ℝ≥0` exponent case with `p = 1 + q`, `q ∈ (0,1)`
  let q : NNReal := ⟨p - 1, sub_nonneg.mpr (le_of_lt hp.1)⟩
  have hq0 : (0 : NNReal) < q := by
    change (0 : ℝ) < p - 1
    exact sub_pos.mpr hp.1
  have hq1 : q < (1 : NNReal) := by
    have : (q : ℝ) < (1 : ℝ) := by
      have : p - 1 < (1 : ℝ) := by linarith [hp.2]
      simpa [q] using this
    exact (NNReal.coe_lt_coe).1 (by simpa using this)
  have hq : q ∈ Set.Ioo (0 : NNReal) 1 := ⟨hq0, hq1⟩
  have hconv :
      ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ ((1 : NNReal) + q)) :=
    _root_.LownerHeinzCore.convexOn_nnrpow_Ioo_one_add  hq
  refine hconv.congr ?_
  intro A hA
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hq0' : (0 : NNReal) < (1 : NNReal) + q :=
    add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt hq0)
  -- `A ^ (1 + q) = A ^ p`
  have hEq :
      A ^ ((1 : NNReal) + q) = A ^ (((1 : NNReal) + q : NNReal) : ℝ) := by
    simpa using (CFC.nnrpow_eq_rpow (A := 𝓐) (a := A) (x := (1 : NNReal) + q) hq0')
  -- simplify the real exponent `(1 + q : ℝ)` into `p`
  have hreal : (((1 : NNReal) + q : NNReal) : ℝ) = p := by
    change (1 : ℝ) + (p - 1) = p
    ring
  simp [hEq, hreal]

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
 lemma cfcR_mul_self (T : 𝓐) (hT : IsSelfAdjoint T) :
    cfcR (fun x : ℝ ↦ x * x) T = T * T := by
  dsimp [cfcR]
  calc
    cfcR (fun x : ℝ ↦ x * x) T =
        cfcR (fun x : ℝ ↦ x) T * cfcR (fun x : ℝ ↦ x) T := by
      simpa using
        (cfc_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (f := fun x : ℝ ↦ x) (g := fun x : ℝ ↦ x) (a := T))
    _ = T * T := by
      simp [cfc_id' (R := ℝ) (a := T) (ha := hT)]

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
 lemma sub_mul_sub (A B : 𝓐) :
    (A - B) * (A - B) = A * A - A * B - B * A + B * B := by
  calc
    (A - B) * (A - B) = (A * A - B * A) - (A * B - B * B) := by
      simp [mul_sub, sub_mul]
    _ = A * A - A * B - B * A + B * B := by
      abel

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
 lemma smul_sub_mul_sub (α : ℝ) (A B : 𝓐) :
    α • (A * A - A * B - B * A + B * B) =
      α • (A * A) - α • (A * B) - α • (B * A) + α • (B * B) := by
  rw [smul_add, smul_sub, smul_sub]

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
 lemma square_convexity_diff_rhs (A B : 𝓐) (u : ℝ) :
    (u * (1 - u)) • ((A - B) * (A - B)) =
      (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
        + (u * (1 - u)) • (B * B) := by
  let α : ℝ := u * (1 - u)
  have hsmul : α • ((A - B) * (A - B)) = α • (A * A - A * B - B * A + B * B) := by
    rw [_root_.LownerHeinzCore.sub_mul_sub  A B]
  have hα :
      α • (A * A) - α • (A * B) - α • (B * A) + α • (B * B)
        =
        (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
          + (u * (1 - u)) • (B * B) := by
    simp [α]
  calc
    (u * (1 - u)) • ((A - B) * (A - B)) = α • ((A - B) * (A - B)) := by simp [α]
    _ = α • (A * A - A * B - B * A + B * B) := hsmul
    _ = α • (A * A) - α • (A * B) - α • (B * A) + α • (B * B) :=
      _root_.LownerHeinzCore.smul_sub_mul_sub  (α := α) A B
    _ = (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
          + (u * (1 - u)) • (B * B) := by
      simp [hα]

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
 lemma square_convexity_diff_hL (A B : 𝓐) (u : ℝ) :
    (1 - u) • (A * A) + u • (B * B) -
        (((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
          + (u * (1 - u)) • (B * A) + (u * u) • (B * B)) =
      (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
        + (u * (1 - u)) • (B * B) := by
  let α : ℝ := u * (1 - u)
  have hα1 : (1 - u) - (1 - u) * (1 - u) = α := by
    simp [α]
    ring
  have hα2 : u - u * u = α := by
    simp [α]
    ring
  have hα3 : (1 - u) * u = α := by
    simp [α]
    ring
  have hAA : (1 - u) • (A * A) - ((1 - u) * (1 - u)) • (A * A) = α • (A * A) := by
    have : (1 - u) • (A * A) - ((1 - u) * (1 - u)) • (A * A) =
        ((1 - u) - (1 - u) * (1 - u)) • (A * A) := by
      simpa using (sub_smul (1 - u) ((1 - u) * (1 - u)) (A * A)).symm
    simp [this, hα1]
  have hBB : u • (B * B) - (u * u) • (B * B) = α • (B * B) := by
    have : u • (B * B) - (u * u) • (B * B) = (u - u * u) • (B * B) := by
      simpa using (sub_smul u (u * u) (B * B)).symm
    simp [this, hα2]
  have hAB : ((1 - u) * u) • (A * B) = α • (A * B) := by simp [hα3]
  have hBA : (u * (1 - u)) • (B * A) = α • (B * A) := by rfl
  have hL :
      (1 - u) • (A * A) + u • (B * B) -
          (((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
            + (u * (1 - u)) • (B * A) + (u * u) • (B * B)) =
        α • (A * A) - α • (A * B) - α • (B * A) + α • (B * B) := by
    have hL0 :
        (1 - u) • (A * A) + u • (B * B) -
            (((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
              + (u * (1 - u)) • (B * A) + (u * u) • (B * B)) =
          ((1 - u) • (A * A) - ((1 - u) * (1 - u)) • (A * A)
              + (u • (B * B) - (u * u) • (B * B)))
            - ((1 - u) * u) • (A * B) - (u * (1 - u)) • (B * A) := by
      abel
    have hL1 :
        ((1 - u) • (A * A) - ((1 - u) * (1 - u)) • (A * A)
              + (u • (B * B) - (u * u) • (B * B)))
            - ((1 - u) * u) • (A * B) - (u * (1 - u)) • (B * A)
          = α • (A * A) - α • (A * B) - α • (B * A) + α • (B * B) := by
      simp_rw [hAA, hBB, hAB, hBA]
      abel
    simpa [hL0] using hL1
  simpa [α] using hL

-- This lemma is purely algebraic, so we drop analytical/finite-dimensional assumptions here.
omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
 lemma square_convexity_diff_hCC_sum (A B : 𝓐) (u : ℝ) :
    ((1 - u) • A) * ((1 - u) • A)
      + ((1 - u) • A) * (u • B)
      + (u • B) * ((1 - u) • A)
      + (u • B) * (u • B) =
      ((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
        + (u * (1 - u)) • (B * A) + (u * u) • (B * B) := by
  have hAA' :
      ((1 - u) • A) * ((1 - u) • A) = ((1 - u) * (1 - u)) • (A * A) := by
    calc
      ((1 - u) • A) * ((1 - u) • A) = (1 - u) • (A * ((1 - u) • A)) := by
        exact Algebra.smul_mul_assoc (R := ℝ) (A := 𝓐) (1 - u) A ((1 - u) • A)
      _ = (1 - u) • ((1 - u) • (A * A)) := by
        rw [Algebra.mul_smul_comm]
      _ = ((1 - u) * (1 - u)) • (A * A) := by
        simp [smul_smul]
  have hAB' :
      ((1 - u) • A) * (u • B) = ((1 - u) * u) • (A * B) := by
    calc
      ((1 - u) • A) * (u • B) = (1 - u) • (A * (u • B)) := by
        exact Algebra.smul_mul_assoc (R := ℝ) (A := 𝓐) (1 - u) A (u • B)
      _ = (1 - u) • (u • (A * B)) := by
        rw [Algebra.mul_smul_comm]
      _ = ((1 - u) * u) • (A * B) := by
        simp [smul_smul]
  have hBA' :
      (u • B) * ((1 - u) • A) = (u * (1 - u)) • (B * A) := by
    calc
      (u • B) * ((1 - u) • A) = u • (B * ((1 - u) • A)) := by
        exact Algebra.smul_mul_assoc (R := ℝ) (A := 𝓐) u B ((1 - u) • A)
      _ = u • ((1 - u) • (B * A)) := by
        simp [Algebra.mul_smul_comm]
      _ = (u * (1 - u)) • (B * A) := by
        simpa using (smul_smul u (1 - u) (B * A))
  have hBB' :
      (u • B) * (u • B) = (u * u) • (B * B) := by
    calc
      (u • B) * (u • B) = u • (B * (u • B)) := by
        exact Algebra.smul_mul_assoc (R := ℝ) (A := 𝓐) u B (u • B)
      _ = u • (u • (B * B)) := by
        simp [Algebra.mul_smul_comm]
      _ = (u * u) • (B * B) := by
        simp [smul_smul]
  rw [hAA', hAB', hBA', hBB']

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
 lemma square_convexity_diff_hCC (A B : 𝓐) (u : ℝ) :
    ((1 - u) • A + u • B) * ((1 - u) • A + u • B) =
      ((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
        + (u * (1 - u)) • (B * A) + (u * u) • (B * B) := by
  have hexpand :
      ((1 - u) • A + u • B) * ((1 - u) • A + u • B) =
        ((1 - u) • A) * ((1 - u) • A)
          + ((1 - u) • A) * (u • B)
          + (u • B) * ((1 - u) • A)
          + (u • B) * (u • B) := by
    set X : 𝓐 := (1 - u) • A
    set Y : 𝓐 := u • B
    have hXY : (1 - u) • A + u • B = X + Y := by simp [X, Y]
    calc
      ((1 - u) • A + u • B) * ((1 - u) • A + u • B) = (X + Y) * (X + Y) := by
        simp [hXY]
      _ = X * (X + Y) + Y * (X + Y) := by
        simp [add_mul]
      _ = (X * X + X * Y) + (Y * X + Y * Y) := by
        simp [mul_add, add_assoc]
      _ = X * X + X * Y + Y * X + Y * Y := by
        abel
      _ = ((1 - u) • A) * ((1 - u) • A)
            + ((1 - u) • A) * (u • B)
            + (u • B) * ((1 - u) • A)
            + (u • B) * (u • B) := by
        simp [X, Y]
  exact hexpand.trans (_root_.LownerHeinzCore.square_convexity_diff_hCC_sum  A B u)

omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] [Nontrivial (𝓐)] in
 lemma square_convexity_diff (A B : 𝓐) (u : ℝ) :
    (1 - u) • (A * A) + u • (B * B)
        - ((1 - u) • A + u • B) * ((1 - u) • A + u • B)
      =
      (u * (1 - u)) • ((A - B) * (A - B)) := by
  rw [_root_.LownerHeinzCore.square_convexity_diff_hCC  A B u]
  have hL' :
      (1 - u) • (A * A) + u • (B * B) -
          (((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
            + (u * (1 - u)) • (B * A) + (u * u) • (B * B)) =
        (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
          + (u * (1 - u)) • (B * B) :=
    _root_.LownerHeinzCore.square_convexity_diff_hL  A B u
  have hR :
      (u * (1 - u)) • ((A - B) * (A - B)) =
        (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
          + (u * (1 - u)) • (B * B) :=
    _root_.LownerHeinzCore.square_convexity_diff_rhs  A B u
  exact hL'.trans hR.symm

omit [Nontrivial (𝓐)] in
 lemma operatorConvexOn_pow_two_Ici :
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ (2 : ℝ)) := by
  dsimp [OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  have hA0 : 0 ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    have : x ∈ Set.Ici (0 : ℝ) := As hx
    simpa [Set.Ici] using this
  have hB0 : 0 ≤ B := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 ?_
    intro x hx
    have : x ∈ Set.Ici (0 : ℝ) := Bs hx
    simpa [Set.Ici] using this
  have hu0' : 0 ≤ (1 - u) := sub_nonneg.mpr hu1
  set C : 𝓐 := (1 - u) • A + u • B
  have hC0 : 0 ≤ C :=
    add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
  have hsq : 0 ≤ (A - B) * (A - B) := by
    have h1 : (0 : 𝓐) ≤ (1 : 𝓐) := (zero_le_one : (0 : 𝓐) ≤ 1)
    have hT : IsSelfAdjoint (A - B) := by simpa using hA.sub hB
    simpa [mul_assoc] using conjugate_isPositive  (X := (1 : 𝓐)) (T := (A - B)) h1 hT
  have hub : 0 ≤ u * (1 - u) := mul_nonneg hu0 hu0'
  have hdiff :
      (1 - u) • (A * A) + u • (B * B) - C * C
        = (u * (1 - u)) • ((A - B) * (A - B)) := by
    simpa [C] using (_root_.LownerHeinzCore.square_convexity_diff  A B u)
  have hnonneg : 0 ≤ (1 - u) • (A * A) + u • (B * B) - C * C := by
    have hscale : 0 ≤ (u * (1 - u)) • ((A - B) * (A - B)) := smul_nonneg hub hsq
    simpa [hdiff] using hscale
  have hmain : C * C ≤ (1 - u) • (A * A) + u • (B * B) :=
    (sub_nonneg).1 hnonneg
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - u)).smul hA |>.add ((IsSelfAdjoint.all u).smul hB)
  -- rewrite the goal via `cfcR (x ↦ x^2) T = T*T`
  have hfun : (fun x : ℝ ↦ x ^ (2 : ℝ)) = (fun x : ℝ ↦ x * x) := by
    funext x
    simp [pow_two]
  rw [hfun]
  simpa [C, _root_.LownerHeinzCore.cfcR_mul_self  C hC, _root_.LownerHeinzCore.cfcR_mul_self  A hA, _root_.LownerHeinzCore.cfcR_mul_self  B hB] using hmain

theorem power_Icc_one_two_operatorConvexOn_Ici : ∀ p ∈ Set.Icc (1 : ℝ) 2,
  OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  by_cases hp1 : p = 1
  · subst hp1
    dsimp [OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hC : IsSelfAdjoint ((1 - u) • A + u • B) := by
      simpa using (IsSelfAdjoint.all (1 - u)).smul hA |>.add ((IsSelfAdjoint.all u).smul hB)
    have hfun : (fun x : ℝ ↦ x ^ (1 : ℝ)) = (fun x : ℝ ↦ x) := by
      funext x
      simp
    rw [hfun]
    simp [cfcR, cfc_id' (R := ℝ) (a := ((1 - u) • A + u • B)) (ha := hC),
      cfc_id' (R := ℝ) (a := A) (ha := hA), cfc_id' (R := ℝ) (a := B) (ha := hB)]
  by_cases hp2 : p = 2
  · subst hp2
    simpa using _root_.LownerHeinzCore.operatorConvexOn_pow_two_Ici
  have hp12 : p ∈ Set.Ioo (1 : ℝ) 2 := by
    refine ⟨?_, ?_⟩
    · have : 1 ≤ p := hp.1
      exact lt_of_le_of_ne this (Ne.symm hp1)
    · have : p ≤ 2 := hp.2
      exact lt_of_le_of_ne this hp2
  dsimp [OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  have hA0 : 0 ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    have : x ∈ Set.Ici (0 : ℝ) := As hx
    simpa [Set.Ici] using this
  have hB0 : 0 ≤ B := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 ?_
    intro x hx
    have : x ∈ Set.Ici (0 : ℝ) := Bs hx
    simpa [Set.Ici] using this
  have hu0' : 0 ≤ (1 - u) := sub_nonneg.mpr hu1
  set C : 𝓐 := (1 - u) • A + u • B
  have hC0 : 0 ≤ C :=
    add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
  have hC_mem : C ∈ Set.Ici (0 : 𝓐) := by
    simpa [C, Set.Ici] using hC0
  have hA_mem : A ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hA0
  have hB_mem : B ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hB0
  have hab : (1 - u) + u = (1 : ℝ) := by ring
  have hconvC : (C ^ p) ≤ (1 - u) • (A ^ p) + u • (B ^ p) := by
    simpa [C] using
      (_root_.LownerHeinzCore.convexOn_rpow_Ioo_one_two  hp12).2 hA_mem hB_mem hu0' hu0 hab
  have hcalc (T : 𝓐) (hT0 : 0 ≤ T) :
      cfcR (fun x : ℝ ↦ x ^ p) T = T ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := T) (y := p) (ha := hT0)).symm
  -- rewrite the convexity inequality through `cfcR`
  simpa [hcalc A hA0, hcalc B hB0, hcalc C hC0, C] using hconvC
end Spectrum
end LownerHeinzCore


