-- Prove2me | solution 1 for Zeta23.Assembly.dyadic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:32:40.614399+00:00
-- url     : https://prove2.me/submissions/9737d6f8-cf19-4325-a72e-89b5c9a053b1

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Assembly
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_TracesBoundsE

-- from Zeta23.Assembly
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# §4 "The counting inequalities" and §6 "Proofs of Theorems A, B, C" — assembly

Reference: the paper, labels `prop:zeroside-rank`, `eq:zeroside-rank`,
`prop:zeroside`, `eq:zeroside`, `eq:zeroside2`, and `sec:proofs` (proofs of `thm:A`, `thm:B`, `thm:C`).

Design:
* Parts A–E of this file are **ζ-free and Defs-free**: theorems about Hermitian matrices
  (Part A, consuming the `RHLinalg` §3 lemmas) and about real numbers / explicit real
  functions (Parts B–E).  Every analytic or combinatorial input produced elsewhere
  (prop:block — `ZeroSide.lean`; prop:tail — `Tail.lean`; thm:traces — `PrimeSideTemp.lean`'s
  `TracesBounds`; Riemann–von Mangoldt and the local count — `Hypotheses.lean`; taper facts —
  `Taper.lean`) enters as an explicit, named hypothesis whose docstring quotes the paper label.
* Part F instantiates A–E with the concrete objects of `Defs.lean`: `thmA_abstract`, `thmB_abstract`,
  `thmC_abstract` (Theorems A–C at fixed `λ < 1` for an abstract `ZeroConfig`, taking prop:block / prop:tail /
  the H-EF bridge / [eq:abdef] / thm:traces as named inputs).
* Error terms are explicit inequalities with named constants throughout Parts A–D; filters /
  `Tendsto` appear only in the final `ε`-wrappers (Part E).

## Units (paper §4, [eq:AE], [eq:hatunits])

Three normalisations of the same real-symmetric `d × d` matrix occur:
* `G` [eq:Gdef];
* `G̃ = G / L`, `Ã = A / L`, `Ẽ = E / L` ("tilde units") — lem:weyl and lem:CS are applied to
  `G̃ = Ã + Ẽ` with threshold `θ = θ₀ ≥ ‖Ẽ‖` (prop:zeroside);
* `Ĝ = G / (a L²)`, `Â`, `Ê` ("hat units", [eq:hatunits]) — lem:ranktrace is applied to `Â = P + Q`
  **only** in these units (paper, after prop:zeroside-rank: "Lemma lem:ranktrace is not
  scale-invariant: it must be applied in the units (eq:hatunits), in which tr P ≤ N_on(I′)").
The two systems meet only through the explicit conversion of Part D,
`tr Ĝ = tr G̃ /(aL)`, `‖Ĝ‖_F² = tr G̃² /(aL)²` (paper §6, first line of the proof of Thm A), and the
taper constant `a` must cancel in `tr Ĝ = N + O(√X / a)`.

Scalar field: `ZeroSide.lean` works over `ℂ` (the inertia argument lives on `ℂ^d`); Part A is kept
`RCLike`-generic like `RHLinalg` and is instantiated at `ℂ` in Part F.
-/

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace Assembly

/-! ## Part A.  Matrix-level counting inequalities (paper §4, "The counting inequalities") -/

section MatrixLevel

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]



end MatrixLevel

/-! ### Frobenius-norm bookkeeping

`RHLinalg.frobSq A = Re tr(Aᴴ A)`.  We identify it with the square of Mathlib's (scoped) Frobenius
norm, to get the triangle inequality `‖Ĝ − Ê‖_F ≤ ‖Ĝ‖_F + ‖Ê‖_F` used in prop:zeroside-rank. -/

section Frob
open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n]







end Frob

section MatrixLevel2

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]




end MatrixLevel2

/-! ## Part B.  The functions `H`, `F` and the `λ₁` versus `λ` step (paper [eq:Fdef], §6)

Vocabulary from `Zeta23/Defs.lean`: `l T = log(T/2π)`, `ell1 T = l T + 2 log 2 − 1`, `Hfun`, `Ffun`,
`P.L T = P.lam * l T`, `P.lam1 T = P.L T / ell1 T`. -/

section HF
open Real















end HF

/-! ## Part C.  §6 at fixed `T`: the explicit inequality for Theorem A

All quantities are real numbers attached to one fixed `T` (and fixed `λ`, `ϱ`); every error term is
explicit.  Dictionary (paper ↔ arguments): `N = N(T,2T)`, `NII = N(I′∖I) := N(T−D₀,T) + N(2T,2T+D₀)`,
`N0star = N₀*(T,2T)`, `s12 = s₁ + s₂`, `trGh = tr Ĝ`, `frGh = ‖Ĝ‖_F²`, `trAh = tr Â`,
`frAh = ‖Â‖_F²`, `B` = the prop:tail bound for `|tr Ê|` and `‖Ê‖_F` (`≤ 2θ₀/L`). -/

section FixedT



end FixedT

/-! ## Part D.  Unit conversion `Ĝ ↔ G̃` and the trace inputs
(paper §6, proof of Thm A, first lines: "In the units (eq:hatunits), `tr Ĝ = tr G̃/(aL)` and
`‖Ĝ‖_F² = tr G̃²/(aL)²`. By Proposition prop:trace, `tr Ĝ = N + O(√X/a)` … (note that the taper
constant `a` cancels). By (eq:tr2) … `‖Ĝ‖_F² ≤ … = (1/λ₁ + λ₁/3) N (1 + O(𝓔′_T))`") -/

section Units
open Complex

variable {m : Type*} [Fintype m]



variable (P : Params) (T : ℝ)








end Units

section TraceInputs




end TraceInputs

/-! ## Part E.  The asymptotic wrappers (the only place filters appear)

E1: the explicit error of Parts C–D is `o(N)` given the growth facts;  E2: `o(N)` error ⇒ `ε`-form;
E3: `λ → 1⁻`;  E4: dyadic summation `N₀*(T,2T) ⇒ N₀*(T)` (paper §6, end of proof of Thm A). -/

section Asymptotic
open Filter Asymptotics Topology









end Asymptotic

/-! ## Part F.  Instantiation with the concrete objects of `Defs.lean`

F2: growth lemmas for the explicit functions `l, L, X` and for `N(T,2T)` under H-RvM;
F3: `thmA_abstract` — Theorem A at fixed `λ < 1` for an abstract `ZeroConfig`, from the named inputs. -/

section Growth
open Filter Asymptotics Topology Real






















end Growth

/-! ### F0.  Window bookkeeping for an abstract `ZeroConfig` (interval additivity; the four
"set-level" facts of prop:zeroside-rank / prop:zeroside:
`s₁+s₂ ≤ N₀*(T,2T) + N(I′∖I)`, `s₁ ≤ N₀ˢ(T,2T) + N(I′∖I)`, `#𝒵(I′) ≤ N_d(T,2T) + N(I′∖I)`,
`N(I′) = N(T,2T) + N(I′∖I)`, where `N(I′∖I) := N(T−D₀,T) + N(2T,2T+D₀)`). -/

section Windows
open Set

variable (Z : ZeroConfig)









variable (T : ℝ)


variable {T}






end Windows

/-! ### F1.  Fixed-`T` assembly with the concrete matrices `Ĝ = P.hat T (Z.Gz P T)` etc.

The inputs from prop:block (ZeroSide.lean) and prop:tail (Tail.lean) are packaged as the two
Prop-structures below, whose fields are exactly the statements those files announce; they are
discharged in those files' instantiation sections. -/

section FixedTConcrete

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

-- `BlockInputs`, `TailInputs`, `NII` live in `Zeta23/Assembly/Inputs.lean` (shared with ZeroSide/Tail).

variable {Z P T}





end FixedTConcrete

/-! ### F3.  Theorem A at fixed `λ < 1` for an abstract zero configuration

The theorems are proved over an abstract error function `Err` (only: eventually nonnegative and
`→ 0`) in place of the concrete `Params.calE` — the `_err` versions below — so that alternative
prime-side chains (e.g. an MV-free one with an enlarged error) plug in directly; the
`calE` statements are kept as specializations. -/

section Main
open Filter Asymptotics Topology

-- `TracesBoundsE` (abstract error rate) and `TracesBounds.toE` live in Zeta23/TracesBoundsE.lean







end Main

/-! ### F4.  Theorems B and C at fixed `λ < 1` for an abstract zero configuration
(the paper §6, proofs of thm:B and thm:C: [eq:nplus-lower] + [eq:zeroside2]) -/

section MainBC
open Filter Asymptotics Topology

variable {m : Type*} [Fintype m]













end MainBC

/-! ### F5.  `𝓔_T → 0` (paper [thm:traces]: "`𝓔_T ≪_λ w/L + T^{λ−1} log l` (λ<1), `≪ w/L + log l/l` (λ=1)") -/

section CalE
open Filter Topology Real



end CalE

end Assembly
end Zeta23

end
open Matrix Finset RHLinalg
open scoped ComplexOrder
open Zeta23
open Assembly
open Filter Asymptotics Topology

theorem solution {f g : ℝ → ℝ → ℝ} {c : ℝ}
    (hf_add : ∀ a b c : ℝ, a ≤ b → b ≤ c → f a c = f a b + f b c)
    (hg_add : ∀ a b c : ℝ, a ≤ b → b ≤ c → g a c = g a b + g b c)
    (hf_nn : ∀ a b, 0 ≤ f a b) (hg_nn : ∀ a b, 0 ≤ g a b)
    (hg_top : Tendsto (fun T => g 0 T) atTop atTop)
    (h : ∀ ε > 0, ∃ T₁, ∀ t ≥ T₁, (c - ε) * g t (2 * t) ≤ f t (2 * t)) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c - ε) * g 0 T ≤ f 0 T := by
  intro ε hε
  by_cases hc : c - ε / 2 < 0
  · refine ⟨0, fun T _ => ?_⟩
    have := hg_nn 0 T; have := hf_nn 0 T
    nlinarith
  have hc : 0 ≤ c - ε / 2 := not_lt.mp hc
  obtain ⟨T₁', hT₁'⟩ := h (ε / 2) (by linarith)
  -- WLOG T₁ ≥ 1
  set T₁ := max T₁' 1 with hT₁def
  have hT₁ : ∀ t ≥ T₁, (c - ε / 2) * g t (2 * t) ≤ f t (2 * t) :=
    fun t ht => hT₁' t ((le_max_left _ _).trans ht)
  have hT₁pos : 0 < T₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- g is monotone in the second argument
  have hg_mono : ∀ a b b', a ≤ b → b ≤ b' → g a b ≤ g a b' := by
    intro a b b' hab hbb'; rw [hg_add a b b' hab hbb']; linarith [hg_nn b b']
  -- induction: f(t, 2^n t) ≥ (c − ε/2) g(t, 2^n t) for t ≥ T₁
  have key : ∀ n : ℕ, ∀ t ≥ T₁, (c - ε / 2) * g t (2 ^ n * t) ≤ f t (2 ^ n * t) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have hf0 : f t t = 0 := by have := hf_add t t t le_rfl le_rfl; linarith
      have hg0 : g t t = 0 := by have := hg_add t t t le_rfl le_rfl; linarith
      simp [hf0, hg0]
    | succ n ih =>
      intro t ht
      have ht0 : 0 ≤ t := hT₁pos.le.trans ht
      have h2n : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hmid : t ≤ 2 ^ n * t := by nlinarith
      have hmid' : 2 ^ n * t ≤ 2 ^ (n + 1) * t := by rw [pow_succ]; nlinarith
      rw [hf_add t (2 ^ n * t) (2 ^ (n + 1) * t) hmid hmid',
        hg_add t (2 ^ n * t) (2 ^ (n + 1) * t) hmid hmid']
      have hstep := hT₁ (2 ^ n * t) (ht.trans hmid)
      have e : 2 * (2 ^ n * t) = 2 ^ (n + 1) * t := by rw [pow_succ]; ring
      rw [e] at hstep
      have := ih t ht
      linarith
  -- choose T₀ so that (ε/2) g(0,T) ≥ (c − ε/2) g(0, 2T₁) for T ≥ T₀, and T₀ ≥ T₁
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp
    (hg_top.eventually_ge_atTop ((c - ε / 2) * g 0 (2 * T₁) * (2 / ε)))
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 ≤ T := hT₁pos.le.trans hTT₁
  -- find n with 2^n T₁ ≤ T < 2^(n+1) T₁
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := T / T₁)
    ((one_le_div hT₁pos).2 hTT₁) one_lt_two
  set t := T / 2 ^ n with htdef
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  have htT₁ : T₁ ≤ t := by
    rw [htdef, le_div_iff₀ h2n]; rw [le_div_iff₀ hT₁pos] at hn1; linarith
  have ht2T₁ : t ≤ 2 * T₁ := by
    rw [htdef, div_le_iff₀ h2n]; rw [div_lt_iff₀ hT₁pos, pow_succ] at hn2; linarith
  have hTt : 2 ^ n * t = T := by rw [htdef]; field_simp
  have ht0 : 0 ≤ t := hT₁pos.le.trans htT₁
  have htT : t ≤ T := by rw [← hTt]; nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := n) (by norm_num)]
  have hk := key n t htT₁
  rw [hTt] at hk
  -- f(0,T) ≥ f(t,T) ≥ (c−ε/2) g(t,T) = (c−ε/2)(g(0,T) − g(0,t)) ≥ (c−ε/2) g(0,T) − (c−ε/2) g(0,2T₁)
  have hf0T : f t T ≤ f 0 T := by rw [hf_add 0 t T ht0 htT]; linarith [hf_nn 0 t]
  have hgsplit : g t T = g 0 T - g 0 t := by rw [hg_add 0 t T ht0 htT]; ring
  have hg0t : g 0 t ≤ g 0 (2 * T₁) := hg_mono 0 t (2 * T₁) ht0 ht2T₁
  have hbig : (c - ε / 2) * g 0 (2 * T₁) * (2 / ε) ≤ g 0 T := hT₂ T ((le_max_right _ _).trans hT)
  have hbig' : (c - ε / 2) * g 0 (2 * T₁) ≤ ε / 2 * g 0 T := by
    have := mul_le_mul_of_nonneg_left hbig (by linarith : 0 ≤ ε / 2)
    calc (c - ε / 2) * g 0 (2 * T₁) = ε / 2 * ((c - ε / 2) * g 0 (2 * T₁) * (2 / ε)) := by
          field_simp
      _ ≤ ε / 2 * g 0 T := this
  calc (c - ε) * g 0 T = (c - ε / 2) * g 0 T - ε / 2 * g 0 T := by ring
    _ ≤ (c - ε / 2) * g 0 T - (c - ε / 2) * g 0 (2 * T₁) := by linarith
    _ ≤ (c - ε / 2) * (g 0 T - g 0 t) := by nlinarith
    _ = (c - ε / 2) * g t T := by rw [hgsplit]
    _ ≤ f t T := hk
    _ ≤ f 0 T := hf0T
