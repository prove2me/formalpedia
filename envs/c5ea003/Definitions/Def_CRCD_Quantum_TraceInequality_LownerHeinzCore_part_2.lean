-- Prove2me | Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_2
-- name    : CRCD_Quantum_TraceInequality_LownerHeinzCore_part_2
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:45:42.822438+00:00
-- url     : https://prove2.me/theorems/2b150332-296d-414d-aafc-d3945bac37a0
-- title:
--   Resolvent concavity and operator concavity of powers from zero to one
-- statement:
--   In the same nontrivial ordered complex C*-algebra $\mathcal A$, with star order and the nonnegative-spectrum class, this part proves concavity of $x\mapsto x/(x+a)$ on the nonnegative spectral domain for every $a>0$, and establishes operator concavity of every power with $0\le p\le1$. Explicitly, for $A,B\ge0$ and $0\le\theta\le1$,
--   $$
--   \bigl((1-\theta)A+\theta B\bigr)^p
--    \ge(1-\theta)A^p+\theta B^p,\qquad 0\le p\le1.
--   $$
--   The powers are the real continuous-functional-calculus powers of positive operators. The endpoint $p=0$ uses the scalar convention $0^0=1$, so the zero power is the identity, including on a kernel; for $p>0$, zero eigenvalues remain zero. The result applies to general C*-algebras under these assumptions, without a finite-dimensional restriction.
--
--   The retained supporting interfaces identify the integral kernel $t^{q-1}x/(x+t)$, for $0<q<1$ and $t>0$, with a positive scalar multiple of the resolvent ratio under nonunital functional calculus. They prove concavity of this operator-valued kernel and of powers for interior exponents, and transfer the result to the endpoint-inclusive scalar-domain predicate. For the later convex-power argument, this part additionally supplies convexity of the shifted inverse map on positive operators and the identity
--   $$
--   \frac{x^2}{x+t}=x-t+\frac{t^2}{x+t}\quad(x+t\ne0),
--   $$
--   together with its functional-calculus form multiplied by $t^{q-1}$. Each use of this integral-kernel representation retains $t>0$ and $0<q<1$.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/TraceInequality/LownerHeinzCore.lean#L725-L1334

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_1

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




theorem ratio_add_t_operatorConcaveOn_Ici : ∀ (t : ℝ), 0 < t →
  OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
    intro t ht
    dsimp [OperatorConcaveOn, OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hu0' : 0 ≤ (1 - u) := sub_nonneg.mpr hu1
    -- main input: operator convexity of `x ↦ 1 / (x + t)` on `Set.Ici 0`
    have hconv_inv :
        cfcR (fun x : ℝ ↦ 1 / (x + t)) ((1 - u) • A + u • B)
          ≤ (1 - u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
            + u • cfcR (fun x : ℝ ↦ 1 / (x + t)) B := by
      simpa using (one_div_add_t_operatorConvexOn_Ici  t ht) (A := A) (B := B) (t := u) hA hB hu0 hu1 As Bs
    -- rewrite `-(x/(x+t))` as `(-1) + t/(x+t)` under functional calculus
    have hcalc (T : 𝓐) (hT : IsSelfAdjoint T) (Ts : spectrum ℝ T ⊆ Set.Ici (0 : ℝ)) :
        cfcR (fun x : ℝ ↦ - (x / (x + t))) T
          = algebraMap ℝ (𝓐) (-1 : ℝ)
            + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) T := by
      let invfun : ℝ → ℝ := fun x ↦ 1 / (x + t)
      have hne0 : ∀ x ∈ spectrum ℝ T, x + t ≠ 0 := by
        intro x hx
        have hx0 : (0 : ℝ) ≤ x := by
          simpa [Set.Ici] using (Ts hx)
        exact ne_of_gt (add_pos_of_nonneg_of_pos hx0 ht)
      have hcont : ContinuousOn invfun (spectrum ℝ T) := by
        simpa [invfun, one_div] using (continuousOn_id.add continuousOn_const).inv₀ hne0
      dsimp [cfcR]
      have hcongr :
          cfcR (fun x : ℝ ↦ - (x / (x + t))) T
            = cfcR
                (fun x : ℝ ↦ (-1 : ℝ) + t * invfun x) T := by
        apply cfc_congr
        intro x hx
        have hx0 : (0 : ℝ) ≤ x := by
          simpa [Set.Ici] using (Ts hx)
        have :
            - (x / (x + t)) = (-1 : ℝ) + t * (1 / (x + t)) := by
          field_simp [ne_of_gt (add_pos_of_nonneg_of_pos hx0 ht)]
          ring_nf
        simpa [invfun] using this
      calc
        cfcR (fun x : ℝ ↦ - (x / (x + t))) T
            = cfcR
                (fun x : ℝ ↦ (-1 : ℝ) + t * invfun x) T := hcongr
        _ = algebraMap ℝ (𝓐) (-1 : ℝ)
              + cfcR (fun x : ℝ ↦ t * invfun x) T := by
            simpa using
              (cfc_const_add (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := (-1 : ℝ))
                (f := fun x : ℝ ↦ t * invfun x) (a := T) (hf := continuousOn_const.mul hcont) (ha := hT))
        _ = algebraMap ℝ (𝓐) (-1 : ℝ)
              + t • cfcR invfun T := by
            simp [cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t) (f := invfun) (a := T)
              (hf := hcont)]
        _ = algebraMap ℝ (𝓐) (-1 : ℝ)
              + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) T := by
            simp [invfun]
    set AB : 𝓐 := (1 - u) • A + u • B
    have hAB : IsSelfAdjoint AB := by
      dsimp [AB]
      simpa using
        (IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) hA).add
          (IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) hB)
    -- apply operator convexity of `-(x/(x+t))`
    have hL :
        cfcR (fun x : ℝ ↦ - (x / (x + t))) AB
          ≤ (1 - u) • cfcR (fun x : ℝ ↦ - (x / (x + t))) A
            + u • cfcR (fun x : ℝ ↦ - (x / (x + t))) B := by
      -- expand both sides using `hcalc`, then use `hconv_inv`
      -- (filled in the next step)
      set C : 𝓐 := algebraMap ℝ (𝓐) (-1 : ℝ)
      have nonneg_of_spectrum_subset_Ici0 {T : 𝓐} (hT : IsSelfAdjoint T)
          (Ts : spectrum ℝ T ⊆ Set.Ici (0 : ℝ)) : 0 ≤ T := by
        have h' : algebraMap ℝ (𝓐) (0 : ℝ) ≤ T :=
          (algebraMap_le_iff_le_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
              (r := (0 : ℝ)) (a := T) (ha := hT)).2 (by
              intro x hx
              simpa [Set.Ici] using (Ts hx))
        simpa using h'
      have hA0 : 0 ≤ A :=
        nonneg_of_spectrum_subset_Ici0 (T := A) hA As
      have hB0 : 0 ≤ B :=
        nonneg_of_spectrum_subset_Ici0 (T := B) hB Bs
      have hAB0 : 0 ≤ AB := by
        dsimp [AB]
        exact add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
      have ABs : spectrum ℝ AB ⊆ Set.Ici (0 : ℝ) := by
        intro x hx
        have hx0 : (0 : ℝ) ≤ x :=
          spectrum_nonneg_of_nonneg (𝕜 := ℝ) (A := 𝓐) (a := AB) hAB0 hx
        simpa [Set.Ici] using hx0
      have hscale :
          t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
            ≤ (t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
              + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B := by
        have hconv_inv_AB :
            cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
              ≤ (1 - u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                + u • cfcR (fun x : ℝ ↦ 1 / (x + t)) B := by
          simpa [AB] using hconv_inv
        have hscale0 :
            t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
              ≤ t •
                  ((1 - u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                    + u • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) :=
          smul_le_smul_of_nonneg_left hconv_inv_AB (le_of_lt ht)
        calc
          t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
              ≤ t •
                  ((1 - u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                    + u • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := hscale0
          _ =
              (t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B := by
            simp [smul_add, smul_smul]
      have hconst : (1 - u) • C + u • C = C := by
        simpa [add_smul, sub_add_cancel] using (add_smul (1 - u) u C).symm
      have hmain :
          C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
            ≤ (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
              + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
        have h' :
            C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
              ≤ C
                + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                  + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
          exact add_le_add_right hscale C
        have hR :
            C
                + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                  + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B)
              =
              (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
          have hR' :
              (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                  + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B)
                =
                ((1 - u) • C + u • C)
                  + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                    + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
            calc
              (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                  + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B)
                  =
                  (1 - u) • C
                    + (1 - u) • (t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                    + (u • C + u • (t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B)) := by
                    simp [smul_add, add_assoc, add_left_comm, add_comm]
              _ =
                  (1 - u) • C
                    + (t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                    + (u • C + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
                    simp [smul_smul, mul_comm, add_assoc, add_left_comm, add_comm]
              _ =
                  ((1 - u) • C + u • C)
                    + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                      + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
                    abel
          calc
            C
                + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                  + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B)
                =
                ((1 - u) • C + u • C)
                  + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                    + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
                  simp [hconst, add_comm]
            _ =
              (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
                  simpa using hR'.symm
        calc
          C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
              ≤
              C
                + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                  + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := h'
          _ =
              (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := hR
      dsimp [C] at hmain
      rw [hcalc AB hAB ABs, hcalc A hA As, hcalc B hB Bs]
      exact hmain
    simpa [AB] using hL



omit [Nontrivial (𝓐)] in
omit [StarOrderedRing 𝓐] in
 lemma cfcₙ_rpowIntegrand₀₁_eq_smul_cfcR_ratio {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1)
    {t : ℝ} (htpos : 0 < t) (X : 𝓐) (hX0 : 0 ≤ X) :
    cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
      (t ^ ((q : ℝ) - 1)) • cfcR (fun x : ℝ => x / (x + t)) X := by
  have hq_real : ((q : ℝ) : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨(NNReal.coe_pos).2 hq.1, (NNReal.coe_lt_coe).2 hq.2⟩
  let ratio : ℝ → ℝ := fun x => x / (x + t)
  let r : ℝ := t ^ ((q : ℝ) - 1)
  have hcont_ratio : ContinuousOn ratio (spectrum ℝ X) :=
    continuousOn_id.div (continuousOn_id.add continuousOn_const) (fun x hx ↦ ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hX0 hx) htpos))
  have hcfcₙ : cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
      cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X := by
    have hqs : quasispectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := quasispectrum_nonneg_of_nonneg X hX0 x hx
      simpa [Set.Ici] using hx0
    have hf : ContinuousOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (quasispectrum ℝ X) :=
      (Real.continuousOn_rpowIntegrand₀₁_Ici hq_real htpos).mono hqs
    simpa using
      (cfcₙ_eq_cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := Real.rpowIntegrand₀₁ (q : ℝ) t) (a := X) (hf := hf) (hf0 := by simp))
  have hEq :
      (spectrum ℝ X).EqOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (fun x : ℝ ↦ r * ratio x) := by
    intro x hx
    simp [r, ratio, Real.rpowIntegrand₀₁_eq_pow_div hq_real (le_of_lt htpos) (spectrum_nonneg_of_nonneg hX0 hx),
      add_comm, mul_div_assoc]
  have hcfc_congr :
      cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
        cfcR (fun x : ℝ ↦ r * ratio x) X :=
    cfc_congr hEq
  have hcfc_mul :
      cfcR (fun x : ℝ ↦ r * ratio x) X =
        r • cfcR ratio X := by
    simpa using
      (cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := r) (f := ratio) (a := X)
        (hf := hcont_ratio))
  have hmain :
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X = r • cfcR ratio X := by
    calc
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
          cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X := by
            simpa using hcfcₙ
      _ = cfcR (fun x : ℝ ↦ r * ratio x) X := hcfc_congr
      _ = r • cfcR ratio X := hcfc_mul
      _ = r • cfcR ratio X := by simp [cfcR]
  simpa [r, ratio] using hmain

 lemma cfcR_ratio_weighted_le {t : ℝ} (htpos : 0 < t) {A B : 𝓐} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • cfcR (fun x : ℝ => x / (x + t)) A + b • cfcR (fun x : ℝ => x / (x + t)) B
      ≤ cfcR (fun x : ℝ => x / (x + t)) (a • A + b • B) := by
  have ha1 : a = 1 - b := by linarith [hab]
  have hb1 : b ≤ 1 := by linarith [ha, hab]
  have hspec (X : 𝓐) (hX0 : 0 ≤ X) : spectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := spectrum_nonneg_of_nonneg hX0 hx
    simpa [Set.Ici] using hx0
  have hOp := ratio_add_t_operatorConcaveOn_Ici (𝓐 := 𝓐) t htpos
  have hneg :=
    (by
      dsimp [OperatorConcaveOn, OperatorConvexOn] at hOp
      have := hOp (A := A) (B := B) (t := b) (IsSelfAdjoint.of_nonneg hA0) (IsSelfAdjoint.of_nonneg hB0)
        hb hb1 (hspec A hA0) (hspec B hB0)
      exact this)
  have hneg' :
      cfcR (fun x : ℝ ↦ - (x / (x + t))) ((1 - b) • A + b • B)
        ≤ (1 - b) • cfcR (fun x : ℝ ↦ - (x / (x + t))) A
          + b • cfcR (fun x : ℝ ↦ - (x / (x + t))) B := hneg
  have hneg'' :
      -cfcR (fun x : ℝ => x / (x + t)) ((1 - b) • A + b • B)
        ≤ -((1 - b) • cfcR (fun x : ℝ => x / (x + t)) A + b • cfcR (fun x : ℝ => x / (x + t)) B) := by
    have h' :
        -cfcR (fun x : ℝ => x / (x + t)) ((1 - b) • A + b • B)
          ≤ -(b • cfcR (fun x : ℝ => x / (x + t)) B + (1 - b) • cfcR (fun x : ℝ => x / (x + t)) A) := by
      simpa [cfcR, cfc_neg, smul_neg, neg_add] using hneg'
    simpa [add_comm, add_left_comm, add_assoc] using h'
  simpa [ha1, add_comm, add_left_comm, add_assoc] using neg_le_neg_iff.mp hneg''

 lemma concaveOn_cfcₙ_rpowIntegrand₀₁ {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1)
    {t : ℝ} (htpos : 0 < t) :
    ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 => cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A) := by
  have hq_real : ((q : ℝ) : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · exact (NNReal.coe_pos).2 hq.1
    · exact (NNReal.coe_lt_coe).2 hq.2
  refine ⟨convex_Ici (𝕜 := ℝ) (0 : 𝓐), ?_⟩
  intro A hA B hB a b ha hb hab
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hB0 : 0 ≤ B := by simpa [Set.Ici] using hB
  have hAB0 : 0 ≤ a • A + b • B := add_nonneg (smul_nonneg ha hA0) (smul_nonneg hb hB0)
  let ratio : ℝ → ℝ := fun x => x / (x + t)
  let r : ℝ := t ^ ((q : ℝ) - 1)
  have hr_nonneg : 0 ≤ r := Real.rpow_nonneg (le_of_lt htpos) _
  have hrepr (X : 𝓐) (hX0 : 0 ≤ X) :
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X = r • cfcR ratio X := by
    simpa [r, ratio] using _root_.LownerHeinzCore.cfcₙ_rpowIntegrand₀₁_eq_smul_cfcR_ratio  (q := q) hq htpos X hX0
  have hratio :
      a • cfcR ratio A + b • cfcR ratio B ≤ cfcR ratio (a • A + b • B) := by
    -- use the separate lemma to keep heartbeats per-declaration small
    -- (`ratio` is a local abbreviation here)
    simpa [ratio] using _root_.LownerHeinzCore.cfcR_ratio_weighted_le  (t := t) htpos (A := A) (B := B) hA0 hB0 ha hb hab
  have hscaled : r • (a • cfcR ratio A + b • cfcR ratio B) ≤ r • cfcR ratio (a • A + b • B) :=
    smul_le_smul_of_nonneg_left hratio hr_nonneg
  have hL :
      a • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A + b • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) B =
        r • (a • cfcR ratio A + b • cfcR ratio B) := by
    simp [hrepr A hA0, hrepr B hB0, smul_add, smul_smul, mul_comm]
  have hR :
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) (a • A + b • B) = r • cfcR ratio (a • A + b • B) := by
    simp [hrepr (a • A + b • B) hAB0]
  calc
    a • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A + b • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) B
        = r • (a • cfcR ratio A + b • cfcR ratio B) := hL
    _ ≤ r • cfcR ratio (a • A + b • B) := hscaled
    _ = cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) (a • A + b • B) := hR.symm

 lemma concaveOn_nnrpow_Ioo {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1) :
    ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ q) := by
  -- integral representation for `a ↦ a ^ q`
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ (A := 𝓐) hq
  let ν : MeasureTheory.Measure ℝ := μ.restrict (Set.Ioi (0 : ℝ))
  let F : ℝ → 𝓐 → 𝓐 := fun t A => cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A
  have hF_int : ∀ A ∈ Set.Ici (0 : 𝓐), MeasureTheory.Integrable (fun t => F t A) ν := by
    intro A hA
    simpa [F, ν, MeasureTheory.IntegrableOn] using (hμ A hA).1
  have hF_conc :
      ∀ᵐ t ∂ν, ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 => F t A) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    simpa [F] using (_root_.LownerHeinzCore.concaveOn_cfcₙ_rpowIntegrand₀₁  (q := q) hq ht)
  have hconc_int :
      ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ ∫ t, F t A ∂ν) :=
    MeasureTheory.integral_concaveOn_of_integrand_ae
      (μ := ν) (s := Set.Ici (0 : 𝓐)) (f := fun t A => F t A)
      (convex_Ici (𝕜 := ℝ) (0 : 𝓐)) hF_conc hF_int
  -- identify the integral with `A ^ q` on `Ici 0`
  refine hconc_int.congr ?_
  intro A hA
  -- `A ^ q` is the set integral of the integrand on `Ioi 0`
  have hEq : A ^ q = ∫ t, F t A ∂ν := by
    simpa [F, ν] using (hμ A hA).2
  simp [hEq]

 lemma concaveOn_rpow_Ioo {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ p) := by
  -- reduce to the `ℝ≥0` exponent case
  let q : NNReal := ⟨p, le_of_lt hp.1⟩
  have hq0 : (0 : NNReal) < q := by
    have : (0 : ℝ) < (q : ℝ) := by
      simpa [q] using hp.1
    exact (NNReal.coe_pos).1 this
  have hq1 : q < (1 : NNReal) := by
    have : (q : ℝ) < (1 : ℝ) := by
      simpa [q] using hp.2
    exact (NNReal.coe_lt_coe).1 (by simpa using this)
  have hq : q ∈ Set.Ioo (0 : NNReal) 1 := ⟨hq0, hq1⟩
  -- main lemma: concavity for `a ↦ a ^ q`
  have hconc : ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ q) :=
    _root_.LownerHeinzCore.concaveOn_nnrpow_Ioo  hq
  -- transport concavity from `A ^ q` to `A ^ p`
  refine hconc.congr ?_
  intro A hA
  -- `A ^ q = A ^ (q : ℝ)`, and `(q : ℝ) = p`
  simpa [q] using (CFC.nnrpow_eq_rpow (A := 𝓐) (a := A) (x := q) hq0)

theorem power_Icc_zero_one_operatorConcaveOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
  OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  by_cases hp0 : p = 0
  · subst hp0
    dsimp [OperatorConcaveOn, OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hC : IsSelfAdjoint ((1 - u) • A + u • B) := by
      simpa using (IsSelfAdjoint.all (1 - u)).smul hA |>.add ((IsSelfAdjoint.all u).smul hB)
    have hfun : (fun x : ℝ ↦ - (x ^ (0 : ℝ))) = (fun _ : ℝ ↦ (-1 : ℝ)) := by
      funext x
      simp
    have hconst (T : 𝓐) (hT : IsSelfAdjoint T) :
        cfcR (fun _ : ℝ ↦ (-1 : ℝ)) T = (-1 : 𝓐) := by
      simpa [cfcR] using
        (cfc_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (-1 : ℝ) T hT)
    rw [hfun]
    rw [hconst _ hC, hconst _ hA, hconst _ hB]
    have hR : (1 - u) • (-1 : 𝓐) + u • (-1 : 𝓐) = (-1 : 𝓐) := by
      calc
        (1 - u) • (-1 : 𝓐) + u • (-1 : 𝓐) = ((1 - u) + u) • (-1 : 𝓐) := by
          simpa [add_smul] using (add_smul (1 - u) u (-1 : 𝓐)).symm
        _ = (1 : ℝ) • (-1 : 𝓐) := by simp
        _ = (-1 : 𝓐) := by simp
    simp
  by_cases hp1 : p = 1
  · subst hp1
    dsimp [OperatorConcaveOn, OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hC : IsSelfAdjoint ((1 - u) • A + u • B) := by
      simpa using (IsSelfAdjoint.all (1 - u)).smul hA |>.add ((IsSelfAdjoint.all u).smul hB)
    have hfun : (fun x : ℝ ↦ - (x ^ (1 : ℝ))) = (fun x : ℝ ↦ -x) := by
      funext x
      simp
    have hneg (T : 𝓐) (hT : IsSelfAdjoint T) :
        cfcR (fun x : ℝ ↦ -x) T = -T := by
      simpa [cfcR] using (cfc_neg_id (R := ℝ) (p := IsSelfAdjoint) (a := T) hT)
    rw [hfun]
    rw [hneg _ hC, hneg _ hA, hneg _ hB]
    -- both sides are `-((1-u)•A + u•B)`
    simp [add_comm, sub_eq_add_neg]
  have hp01 : p ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have : 0 ≤ p := hp.1
      exact lt_of_le_of_ne this (Ne.symm hp0)
    · have : p ≤ 1 := hp.2
      exact lt_of_le_of_ne this hp1
  dsimp [OperatorConcaveOn, OperatorConvexOn]
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
  have hC0 : 0 ≤ (1 - u) • A + u • B :=
    add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
  set C : 𝓐 := (1 - u) • A + u • B
  have hC_mem : C ∈ Set.Ici (0 : 𝓐) := by
    simpa [C, Set.Ici] using hC0
  have hA_mem : A ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hA0
  have hB_mem : B ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hB0
  have hconcC : (1 - u) • (A ^ p) + u • (B ^ p) ≤ C ^ p := by
    have hab : (1 - u) + u = (1 : ℝ) := by ring
    simpa [C] using (_root_.LownerHeinzCore.concaveOn_rpow_Ioo  hp01).2 hA_mem hB_mem hu0' hu0 hab
  have hcalc (T : 𝓐) (hT0 : 0 ≤ T) :
      cfcR (fun x : ℝ ↦ x ^ p) T = T ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := T) (y := p) (ha := hT0)).symm
  have hconcC' :
      (1 - u) • cfcR (fun x : ℝ ↦ x ^ p) A + u • cfcR (fun x : ℝ ↦ x ^ p) B
        ≤ cfcR (fun x : ℝ ↦ x ^ p) C := by
    simpa [hcalc A hA0, hcalc B hB0, hcalc C hC0, C] using hconcC
  -- convert concavity into convexity of `x ↦ -x^p`
  simpa [cfcR, cfc_neg, smul_neg, neg_add, add_assoc, add_left_comm, add_comm] using neg_le_neg hconcC'

 lemma sq_mul_div_add (x t : ℝ) (hxt : x + t ≠ 0) :
    (x * x) / (x + t) = x - t + (t * t) / (x + t) := by
  field_simp [hxt]
  ring

 lemma convexOn_cfcR_one_div_add_t (t : ℝ) (htpos : 0 < t) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ cfcR (fun x : ℝ ↦ 1 / (x + t)) X) := by
  have hs : Convex ℝ (Set.Ici (0 : 𝓐)) := convex_Ici (𝕜 := ℝ) (0 : 𝓐)
  refine ⟨hs, ?_⟩
  intro A hA B hB a b ha hb hab
  have ha1 : a = 1 - b := by linarith [hab]
  have hb1 : b ≤ 1 := by linarith [ha, hab]
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hB0 : 0 ≤ B := by simpa [Set.Ici] using hB
  have hspec (X : 𝓐) (hX0 : 0 ≤ X) : spectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := spectrum_nonneg_of_nonneg hX0 hx
    simpa [Set.Ici] using hx0
  have hOp := one_div_add_t_operatorConvexOn_Ici (𝓐 := 𝓐) t htpos
  dsimp [OperatorConvexOn] at hOp
  simpa [one_div, ha1] using
    hOp (A := A) (B := B) (t := b) (IsSelfAdjoint.of_nonneg hA0) (IsSelfAdjoint.of_nonneg hB0) hb hb1 (hspec A hA0) (hspec B hB0)

omit [Nontrivial (𝓐)] in
 lemma G_eqOn_rpowIntegrand₀₁_mul {q : NNReal} (hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (htpos : 0 < t) :
    (Set.Ici (0 : 𝓐)).EqOn
      (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X)
      (fun X : 𝓐 ↦ (t ^ ((q : ℝ) - 1)) •
        (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X)) := by
  intro X hX
  have hX0 : 0 ≤ X := by simpa [Set.Ici] using hX
  have hX_sa : IsSelfAdjoint X := IsSelfAdjoint.of_nonneg hX0
  have hqs : quasispectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := quasispectrum_nonneg_of_nonneg X hX0 x hx
    simpa [Set.Ici] using hx0
  have hf_int : ContinuousOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (quasispectrum ℝ X) :=
    (Real.continuousOn_rpowIntegrand₀₁_Ici hq_real htpos).mono hqs
  have hf :
      ContinuousOn (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) (quasispectrum ℝ X) :=
    continuousOn_id.mul hf_int
  have hcfcₙ :
      cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X =
        cfcR
          (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X := by
    simpa using
      (cfcₙ_eq_cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) (a := X)
        (hf := hf) (hf0 := by simp))
  have hEq :
      (spectrum ℝ X).EqOn (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x)
        (fun x : ℝ ↦ (t ^ ((q : ℝ) - 1)) * (x - t + (t ^ (2 : ℕ)) / (x + t))) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := spectrum_nonneg_of_nonneg hX0 hx
    have ht0 : (0 : ℝ) ≤ t := le_of_lt htpos
    have hxt : x + t ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hx0 htpos)
    have hdiv : (x * x) / (x + t) = x - t + (t * t) / (x + t) := _root_.LownerHeinzCore.sq_mul_div_add x t hxt
    have hrepr0 :
        x * Real.rpowIntegrand₀₁ (q : ℝ) t x = (t ^ ((q : ℝ) - 1)) * ((x * x) / (x + t)) := by
      rw [Real.rpowIntegrand₀₁_eq_pow_div hq_real ht0 hx0]
      rw [mul_div_assoc']
      have hnum : x * (t ^ ((q : ℝ) - 1) * x) = t ^ ((q : ℝ) - 1) * (x * x) := by ring
      rw [hnum, mul_div_assoc]
      simp [add_comm]
    simp [hrepr0, hdiv, pow_two, mul_comm]
  have hcfc_congr :
      cfcR
          (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X
        =
        cfcR
          (fun x : ℝ ↦ (t ^ ((q : ℝ) - 1)) * (x - t + (t ^ (2 : ℕ)) / (x + t))) X :=
    cfc_congr hEq
  have hne : ∀ x ∈ spectrum ℝ X, x + t ≠ 0 := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := spectrum_nonneg_of_nonneg hX0 hx
    exact ne_of_gt (add_pos_of_nonneg_of_pos hx0 htpos)
  have hcont_one_div : ContinuousOn (fun x : ℝ ↦ 1 / (x + t)) (spectrum ℝ X) := by
    have hden : ContinuousOn (fun x : ℝ ↦ x + t) (spectrum ℝ X) :=
      continuousOn_id.add continuousOn_const
    exact continuousOn_const.div hden hne
  have hcont_inner :
      ContinuousOn (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) (spectrum ℝ X) := by
    have hden : ContinuousOn (fun x : ℝ ↦ x + t) (spectrum ℝ X) :=
      continuousOn_id.add continuousOn_const
    have hdiv : ContinuousOn (fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) (spectrum ℝ X) :=
      continuousOn_const.div hden hne
    have hsub : ContinuousOn (fun x : ℝ ↦ x - t) (spectrum ℝ X) :=
      continuousOn_id.sub continuousOn_const
    exact hsub.add hdiv
  have hcfc_scale :
      cfcR
          (fun x : ℝ ↦ (t ^ ((q : ℝ) - 1)) * (x - t + (t ^ (2 : ℕ)) / (x + t))) X
        =
        (t ^ ((q : ℝ) - 1)) • cfcR
          (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) X := by
    simpa using
      (cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := (t ^ ((q : ℝ) - 1)))
        (f := fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) (a := X)
        (hf := hcont_inner))
  have hcfc_inner :
      cfcR
          (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) X
        =
        X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X := by
    have hconst :
        cfcR (fun _ : ℝ ↦ t) X =
          algebraMap ℝ (𝓐) t := by
      simpa using (cfc_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t) (a := X) hX_sa)
    have hid :
        cfcR (fun x : ℝ ↦ x) X = X := by
      simpa using (cfc_id' (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := X) (ha := hX_sa))
    have hpow :
        cfcR
            (fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) X
          =
          (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X := by
      have :
          cfcR
              (fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) X
            =
            cfcR
              (fun x : ℝ ↦ (t ^ (2 : ℕ)) * (1 / (x + t))) X := by
        refine cfc_congr ?_
        intro x hx
        simp [div_eq_mul_inv, mul_comm]
      rw [this]
      simpa [cfcR] using
        (cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (r := (t ^ (2 : ℕ))) (f := fun x : ℝ ↦ 1 / (x + t)) (a := X) (hf := hcont_one_div))
    calc
      cfcR
          (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) X
          =
          cfcR (fun x : ℝ ↦ x - t) X
            + cfcR (fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) X := by
            simpa using
              (cfc_add (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
                (f := fun x : ℝ ↦ x - t) (g := fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) (a := X))
      _ =
          (cfcR (fun x : ℝ ↦ x) X
            - cfcR (fun _ : ℝ ↦ t) X)
            + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X := by
            simpa [hpow] using
              (congrArg (fun z => z + cfcR
                (fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) X)
                (cfc_sub (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
                  (f := fun x : ℝ ↦ x) (g := fun _ : ℝ ↦ t) (a := X)))
      _ = X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X := by
          simp [hid, hconst, sub_eq_add_neg, add_comm]
  -- finish
  calc
    cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X
        =
        cfcR
          (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X := hcfcₙ
    _ =
        cfcR
          (fun x : ℝ ↦ (t ^ ((q : ℝ) - 1)) * (x - t + (t ^ (2 : ℕ)) / (x + t))) X := hcfc_congr
    _ =
        (t ^ ((q : ℝ) - 1)) • cfcR
          (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) X := hcfc_scale
    _ = (t ^ ((q : ℝ) - 1)) •
        (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X) := by
        simp [hcfc_inner, smul_add, smul_smul, mul_comm]
end Spectrum
end LownerHeinzCore


