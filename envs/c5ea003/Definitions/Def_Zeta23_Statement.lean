-- Prove2me | Definitions.Def_Zeta23_Statement
-- name    : Zeta23_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-16T14:43:23.498902+00:00
-- url     : https://prove2.me/theorems/168c9878-98fd-4610-9af7-49e0b514d0d1
-- title:
--   Zeta23 — nontrivial zeros of ζ and the counting functions
-- statement:
--   The objects Theorems A–C speak about, defined directly against Mathlib.
--
--   A point $\rho$ is a **nontrivial zero** when $\zeta(\rho)=0$ and $0<\operatorname{Re}\rho<1$; its
--   **multiplicity** $m_\rho$ is the order of vanishing of $\zeta$ at $\rho$, taken from Mathlib's
--   `analyticOrderAt`. Over the window $T_1 < \operatorname{Im}\rho \le T_2$ this file defines
--   $$N = \sum_\rho m_\rho,\quad N_d = \#\{\rho\},\quad
--   N_0 = \sum_{\operatorname{Re}\rho = 1/2} m_\rho,\quad
--   N_0^* = \#\{\rho : \operatorname{Re}\rho = \tfrac12\},\quad
--   N_0^s = \#\{\rho : \operatorname{Re}\rho = \tfrac12,\ m_\rho = 1\},$$
--   the counting functions of the critical-line literature. It also carries `ZetaSeam`, the structure
--   recording the classical facts about $\zeta$ that let these counts be read as an abstract zero
--   configuration.
-- source:
--   Claude (Anthropic, San Francisco, 2026), "More than two thirds of the zeros of the Riemann zeta function lie on the critical line", §1 [Results] and [eq:trivialchain]. Formalization: https://github.com/anthropics/zeta-23-lean/blob/be438afd1a8bf3d80259428251be21e050d85db6/Zeta23/Statement.lean#L1-L190

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
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
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement.lean — the statement layer.

Canonical text: the paper, §1 [Results], [eq:trivialchain], [thm:A], [thm:B], [thm:C].

It (1) defines nontrivial zeros, multiplicity (via analyticOrderAt) and the six counting functions of
§1 directly against Mathlib; (2) packages the "seam" facts needed to view them as an abstract
Zeta23.ZeroConfig (structure ZetaSeam — classical facts about ζ, established from Mathlib elsewhere in
the repository, not paper inputs); (3) states Theorems A, B, C in ε-form (fixed λ ∈ (0,1) with
constant H(λ), F(λ), then the 2/3, 1/2, 3/4 liminf wrappers via λ → 1⁻);
(4) proves the sanity anchors connecting to Mathlib's RiemannHypothesis and [eq:trivialchain].
-/

open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

namespace Zeta23

/-! ## 1. Nontrivial zeros and multiplicity, against Mathlib -/

/-- ρ is a nontrivial zero of ζ: "ρ = β + iγ runs over the nontrivial zeros of ζ(s)" [Results],
rendered as ζ(ρ) = 0 with 0 < Re ρ < 1 (the critical strip). Mathlib's RiemannHypothesis phrases
"nontrivial" as "not of the form −2(n+1) and ≠ 1"; every strip zero is nontrivial in that sense
(lemma IsNontrivialZero.not_trivial below); the converse (all such zeros lie in the open strip) is
classical (nonvanishing on Re s ≥ 1 and, via the functional equation, on Re s ≤ 0) and is not
needed for the statements. -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- m_ρ, "the multiplicity of ρ" [Results]: the order of vanishing of ζ at ρ, via Mathlib's
analyticOrderAt (ℕ∞-valued; toNat sends ⊤ to 0, so 1 ≤ zeroMult ρ encodes BOTH "ζ is not locally
identically zero at ρ" and "ρ is a zero" — see ZetaSeam.one_le_mult). -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- {ρ nontrivial zero : T₁ < γ ≤ T₂}, γ = Im ρ  [Results] (positive-ordinate window; NOT |γ|). -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂} "(counted with multiplicity)"  [Results]. -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- N_d(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂} "(each distinct point counted once)"  [Results]. -/
def Ndist (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂).ncard

/-- N₀(T₁,T₂) := "the number of zeros on the critical line with T₁ < γ ≤ T₂ counted with …
multiplicity"  [Results]. -/
def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeroMult ρ

/-- N₀*(T₁,T₂) := same "without multiplicity"  [Results]. This is what Theorem A bounds. -/
def N0star (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

/-- N₀ˢ(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂, β = 1/2, m_ρ = 1}  [Results]. -/
def N0simple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

/-- Nˢ(T₁,T₂) := "the number of simple zeros" with T₁ < γ ≤ T₂  [Results]. -/
def Nsimple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | zeroMult ρ = 1}).ncard

/-! ## 2. The seam: ζ's zeros as an abstract ZeroConfig -/

/-- Classical facts about ζ needed to instantiate Zeta23.ZeroConfig; these are established from
Mathlib elsewhere in the repository (identity theorem + ζ(2) ≠ 0 for one_le_mult; functional equation
riemannZeta_one_sub / completedRiemannZeta_one_sub + Γ-nonvanishing + conjugation symmetry at the
level of analyticOrderAt for the reflection facts; isolated zeros + the pole at 1 for finiteness),
and are not inputs of the paper. Paper [subsec:weil]: "The multiset {(γ_ρ,m_ρ)} is invariant under
γ ↦ γ̄ (i.e. ρ ↦ 1−ρ̄; multiplicities agree because conj ξ(conj s) = ξ(s) = ξ(1−s))". -/
structure ZetaSeam : Prop where
  /-- H-fin: at a nontrivial zero the analytic order is finite and ≥ 1. -/
  one_le_mult : ∀ ρ, IsNontrivialZero ρ → 1 ≤ zeroMult ρ
  /-- H-symm (set): ρ ↦ 1 − conj ρ preserves nontrivial zeros. -/
  reflect_zero : ∀ ρ, IsNontrivialZero ρ → IsNontrivialZero (reflect ρ)
  /-- H-symm (multiplicity). -/
  mult_reflect : ∀ ρ, IsNontrivialZero ρ → zeroMult (reflect ρ) = zeroMult ρ
  /-- local finiteness: finitely many nontrivial zeros with T₁ < γ ≤ T₂. -/
  finite_window : ∀ T₁ T₂ : ℝ, ({ρ | IsNontrivialZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

/-- The nontrivial zeros of ζ with their multiplicities, as an abstract zero configuration.
carrier := {ρ | IsNontrivialZero ρ} exactly, mult := zeroMult exactly (seam requirement: H-EF's
W then ranges over exactly the nontrivial zeros weighted by exactly the analytic order). -/
def zetaZeros (hs : ZetaSeam) : ZeroConfig where
  carrier := {ρ | IsNontrivialZero ρ}
  mult := zeroMult
  one_le_mult := hs.one_le_mult
  strip := fun _ h => ⟨h.2.1.le, h.2.2.le⟩
  reflect_mem := hs.reflect_zero
  mult_reflect := hs.mult_reflect
  finite_window := hs.finite_window

section seam_rfl
variable (hs : ZetaSeam) (T₁ T₂ : ℝ)




end seam_rfl

/-! ## 3. Sanity anchors (connection to Mathlib's existing statement of RH) -/

/-- A strip zero is a "nontrivial zero" in the sense inlined in Mathlib's RiemannHypothesis:
not a trivial zero −2(n+1) (those have real part ≤ −2) and not the pole 1. -/
lemma IsNontrivialZero.not_trivial {ρ : ℂ} (h : IsNontrivialZero ρ) :
    (¬∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨n, rfl⟩
    have := h.2.1
    simp at this
    linarith
  · rintro rfl
    simpa using h.2.2




/-! ## 4. Theorems A, B, C

The headline theorems Zeta23.thmA, thmA_cumulative, thmA_lam, thmB, thmB_cumulative, thmB_lam, thmC,
thmC_cumulative, thmC_lam are proved in Zeta23/Final.lean (their types display the full trust base:
literature explicit formula, Riemann–von Mangoldt, Montgomery–Vaughan, Γ-facts), on top of the
versions Zeta23.thmA_of_traces etc. in Zeta23/Main.lean (thm:traces as an explicit hypothesis). This file
stays light (definitions + anchors) so that it can be read and imported cheaply.

Paper [thm:A], verbatim: "Let 0 < λ ≤ 1 be fixed. There are constants c(λ) > 0 and T₀(λ) such that
for all T ≥ T₀(λ)   N₀*(T,2T) ≥ (H(λ) − c(λ) loglogT/logT) N(T,2T),
and for λ < 1 the factor loglog T may be omitted. In particular
  liminf_{T→∞} N₀*(T,2T)/N(T,2T) ≥ 2/3,   liminf_{T→∞} N₀*(T)/N(T) ≥ 2/3".
Formal target: the ε-forms, for each fixed λ ∈ (0,1) with constant
H(λ) (resp. 2F(λ)−1, F(λ)), which absorb c(λ)/log T; then the 2/3 (resp. 1/2, 3/4) forms via
sup_{λ<1} H(λ) = H(1) = 2/3 etc. The effective c(λ) forms are not stated. -/




end Zeta23


