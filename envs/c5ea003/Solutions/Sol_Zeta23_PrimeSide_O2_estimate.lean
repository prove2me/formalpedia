-- Prove2me | solution 1 for Zeta23.PrimeSide.O2_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:08:15.992121+00:00
-- url     : https://prove2.me/submissions/9fae2cf1-dcd8-4077-9937-d48e5f58c6f7

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PP
import Definitions.Def_Zeta23_PrimeSideB_PPKernel
import Theorems.Thm_Zeta23_PrimeSide_abs_Aplus_le

-- from Zeta23.PrimeSideB.PPKernel
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# Kernel lemmas for [prop:PP] (§5.4)

Pure measure-theory / trigonometric-integral / H-MV-application lemmas used by
`Zeta23/PrimeSideB/PP.lean`.

* `sqIntegral_shear`: the substitution `τ = τ' + x` on the square `I×I` (§5.4).
* `intervalIntegral_cos_linear*`: `∫_α^β cos(θt + c) dt` closed forms and the bound `2/|θ|` (§5.4).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate

namespace Zeta23
namespace PrimeSide

/-! ## Elementary facts about the index range `primeRange X = Finset.Ioc 0 ⌊X⌋₊` -/

section Basics

lemma one_le_of_mem_primeRange {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) : 1 ≤ n :=
  (Finset.mem_Ioc.mp hn).1





lemma acoef_nonneg (n : ℕ) : 0 ≤ acoef n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)



/-- Λ(1) = 0, so a_1 = 0: terms with n = 1 never contribute. -/
lemma acoef_one : acoef 1 = 0 := by simp [acoef, ArithmeticFunction.vonMangoldt_apply_one]

lemma acoef_eq_zero_or_two_le {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) :
    acoef n = 0 ∨ 2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · left
    have : n = 1 := by have := one_le_of_mem_primeRange hn; omega
    subst this; exact acoef_one
  · exact Or.inr h

end Basics

/-! ## The shear `(τ,τ') ↦ (x,τ') = (τ−τ',τ')` on `I × I`  (§5.4) -/

section Shear
variable {Φ : ℝ → ℝ} {T : ℝ}











end Shear

/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/

section CosIntegral









variable {T : ℝ}


end CosIntegral

/-! ## Per-frequency-pair decomposition of `𝓜[cos(·y), cos(·y')]`  ([eq:MPP], §5.4) -/

section PairDecomp
variable {Φ : ℝ → ℝ} {T : ℝ}






/-! ### The diagonal 𝒟 (§5.4) -/



/-! ### The sum-frequency terms 𝒪₂ (§5.4) -/


/-! ### The difference-frequency terms 𝒪₁, exact evaluation (§5.4) -/






end PairDecomp

/-! ## Applying H-MV on the prime-power frequencies  ([lem:MV], [eq:deltan]; §5.1, §5.4) -/

section MVapply
variable {C : ℝ}





end MVapply

end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideB.PP
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Prime side, part B/PP — paper §5 [prop:PP] (§5.4): the term 𝓜[P_X,P_X]

Consumed by `Zeta23/PrimeSideB.lean` ([thm:traces]) through the three results at the bottom of
this file:

* `prop_PP`        [prop:PP] first form (§5.4):
      𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L²X);
* `sum_a2g_lower`, `sum_a2g_upper`  (§5.4, the "Finally" step, from [eq:gbounds]+[eq:cheb2]):
      (L−2w)³/6 − C·L² ≤ Σ_{n≤X} Λ(n)²/n · g(log n) ≤ L³/6 + C·L²,
  which give the paper's second form  𝓜[P_X,P_X] = (TL³/6π)(1+O(w/L)) + O(L²X).

Everything is stated in the abstract prime-side layer (Zeta23/PrimeSideA/Defs.lean +
`LocalHyps`/`EventuallyAt` of Zeta23/PrimeSideA.lean): `p : Setting` = (T, λ, w), `F : LocalFun` =
the taper data (φ̂, Φ, A_φ, g, a, b) subject to `LocalHyps cϱ p F` (the facts [eq:psidef],
[eq:abdef], [eq:gbounds], [eq:Phi2FT], …, each a proof obligation of Zeta23/Taper.lean, not an
axiom).  `P_X` is `Zeta23.PX` [eq:Pdef] of Zeta23/Defs.lean and 𝓜[·,·] is
`Zeta23.PrimeSide.Mform` (§5.4).  Analytic inputs: H-cheb = `Zeta23.ChebyshevMertens` [lem:cheb]
and H-MV = `Zeta23.MVHilbert` [lem:MV] from Zeta23/Hypotheses.lean (fields of `PaperInputs`).

## Proof route (paper §5.4, reorganised for Lean; labels as in the paper)
1. Bilinearity:  𝓜[P_X,P_X] = π⁻² Σ_{n,m≤X} a_n a_m 𝓜[cos(·y_n), cos(·y_m)],  a_n = Λ(n)/√n, y_n = log n.
2. Shear `(τ,τ') ↦ (x,τ') := (τ−τ',τ')` (measure-preserving on ℝ²) + Fubini  (§5.4 "Substituting
   τ = τ'+x … τ' ranges over I∩(I−x) = [T+x⁻, 2T−x⁺]"):
      𝓜[u,v] = ∫_{|x|≤T} Φ(x)² ∫_{max(T,T−x)}^{min(2T,2T−x)} u(τ'+x) v(τ') dτ' dx.
3. cos A cos B = ½cos(A−B) + ½cos(A+B): inner integral = ½J(xy_n, y_n−y_m) + ½J(xy_n, y_n+y_m),
   J(c,θ) := ∫_α^β cos(c+θτ')dτ' = (β−α)cos c (θ=0), = [sin(c+θβ)−sin(c+θα)]/θ (θ≠0), |J| ≤ 2/|θ|.
4. 𝒟 (n=m, "−"):  ½∫_{|x|≤T}Φ²(T−|x|)cos(xy_n) = πT g(y_n) + O(∫Φ²|x|)   by [eq:Phi2FT];
   𝒪₂ (all n,m, "+"):  ≤ (∫Φ²)(Σa_n)²/(2π² log 2) ≪ XL                        by [eq:cheb1];
   𝒪₁ (n≠m, "−"):  an explicit combination of 8 sums Σ_{n≠m} x_n conj(z_m)/(y_n−y_m) with
   |x_n| = a_n, |z_m| ≤ a_m ∫Φ², each ≤ C_MV·(∫Φ²)·Σ a_n²/δ_n with δ_n = 1/(2n) [eq:deltan] ≪ L²X by H-MV
   and [eq:cheb1] (Σ Λ(n)² ≪ X log X).
Constants: the paper's O(L²X) constant (and the λ=1 "18/L" sharpness) is not load-bearing;
we prove ∃ C.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

variable {cϱ lam : ℝ}

/-! ## The main-term sum  Σ_{n≤X} a_n² g(y_n) = Σ_{n≤X} Λ(n)²/n · g(log n)   (§5.4) -/



/-! ## Elementary facts about the index range and `X = e^L` -/

section Basics
variable {p : Setting} {F : LocalFun}





end Basics

/-! ## The g-sandwich  (§5.4)

"Finally, by [eq:gbounds] and [eq:cheb2] (note a_n² = Λ(n)²/n),
  (L−2w)³/6 + O(L²) = Σ_{n≤Xe^{−2w}} a_n²(L−2w−y_n) ≤ Σ_{n≤X} a_n² g(y_n) ≤ Σ_{n≤X} a_n²(L−y_n) = L³/6+O(L²)". -/

section Sandwich
variable {p : Setting} {F : LocalFun}



end Sandwich

/-! ## Assembly of [prop:PP]  (§5.4) -/

section Assembly
variable {Φ : ℝ → ℝ} {T : ℝ}





end Assembly

/-! ## Results consumed by PrimeSideB.lean -/

section Results




end Results


end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ lam : ℝ}
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem solution (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (X T : ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)|
      ≤ (∫ x, Φ x ^ 2) / Real.log 2 * (∑ n ∈ primeRange X, acoef n) ^ 2 := by
  have hW : 0 ≤ ∫ x, Φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hper : ∀ n ∈ primeRange X, ∀ m ∈ primeRange X,
      |acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)|
        ≤ acoef n * acoef m * ((∫ x, Φ x ^ 2) / Real.log 2) := by
    intro n hn m hm
    rw [abs_mul, abs_mul, abs_of_nonneg (acoef_nonneg n), abs_of_nonneg (acoef_nonneg m)]
    rcases acoef_eq_zero_or_two_le hn with h0 | hn2
    · simp [h0]
    rcases acoef_eq_zero_or_two_le hm with h0 | hm2
    · simp [h0]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (acoef_nonneg n) (acoef_nonneg m))
    have hyn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hym : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
    have hpos : 0 < Real.log n + Real.log m := by linarith
    calc |Aplus Φ T (Real.log n) (Real.log m)|
        ≤ 2 / (Real.log n + Real.log m) * ∫ x, Φ x ^ 2 := abs_Aplus_le hΦ hΦ2 hpos
      _ ≤ 2 / (2 * Real.log 2) * ∫ x, Φ x ^ 2 := by gcongr; linarith
      _ = (∫ x, Φ x ^ 2) / Real.log 2 := by field_simp
  calc |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)|
      ≤ ∑ n ∈ primeRange X, |∑ m ∈ primeRange X,
          acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          |acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)| :=
        Finset.sum_le_sum fun n _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          acoef n * acoef m * ((∫ x, Φ x ^ 2) / Real.log 2) :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hper n hn m hm
    _ = (∫ x, Φ x ^ 2) / Real.log 2 * (∑ n ∈ primeRange X, acoef n) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
