-- Prove2me | Definitions.Def_Nonadditivity_Linearization
-- name    : Nonadditivity_Linearization
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:00.813482+00:00
-- url     : https://prove2.me/theorems/ff686f56-e3c0-46ab-9802-f961353e0b4b
-- title:
--   Reduced-word types and finite polynomial-support operations
-- statement:
--   Let $L=\{0,1,2,3\}$, with inverse $a^{-1}=3-a$, and set $F(a)=\{b\in L:b\ne a^{-1}\}$. Reduced tails satisfy
--   $$T_a(0)=\{\ast\},\qquad T_a(m+1)=\coprod_{b\in F(a)}T_b(m),\qquad |F(a)|=3,\quad |T_a(m)|=3^m.$$
--   A nonempty reduced word of length $m+1$ is a first letter together with such a tail. The bundle provides finite type structures and the inverse-involution identity. For a finite subset $S$ of a group $G$, it also defines
--   $$S^{-1}S=\{g^{-1}h:g,h\in S\}$$
--   and proves its membership characterization. Finally, for real scalars $x,y$, the nonnegative relative norm error is $\max\{0,x/y-1\}$. These discrete types, support operations, and scalar error quantities are the imported combinatorial infrastructure for polynomial reductions.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/Linearization.lean#L48-L427

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/



















/-!
# Algebraic and numerical steps in polynomial linearization

This file proves the finite support bound, Gram factorization identities,
Hermitian dilation identities, the scalar backward-error calculation, and the
geometric word-count calculation used in Sections 3 and Appendix A of
`nonadditivity.tex`.

The analytic existence of the positive block matrix with the stated operator
norm bound is not assumed globally or declared as an axiom here. The Gram
identities below apply to any supplied square-root factor; the error theorem
states its norm-identity hypotheses explicitly.
-/

set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.Linearization

open scoped BigOperators

section Support

variable {G : Type*} [Group G] [DecidableEq G]

/-- The finite set `S⁻¹ S`, represented without a pointwise-set convention. -/
def differenceSupport (S : Finset G) : Finset G :=
  (S ×ˢ S).image (fun gh => gh.1⁻¹ * gh.2)

@[simp] theorem mem_differenceSupport {S : Finset G} {w : G} :
    w ∈ differenceSupport S ↔ ∃ g ∈ S, ∃ h ∈ S, g⁻¹ * h = w := by
  simp only [differenceSupport, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨g,h⟩, ⟨hg,hh⟩, hw⟩
    exact ⟨g,hg,h,hh,hw⟩
  · rintro ⟨g,hg,h,hh,hw⟩
    exact ⟨(g,h), ⟨hg,hh⟩, hw⟩









end Support

section Gram

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
variable {A : Type*} [NonUnitalSemiring A] [StarRing A]







end Gram

section PositiveMatrices

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν]









end PositiveMatrices

section Dilation

variable {ι : Type*} [Fintype ι]
variable {A : Type*} [NonUnitalSemiring A] [StarRing A]







end Dilation

section ErrorTransfer





/-- Nonnegative relative excess used for every intermediate polynomial. -/
noncomputable def relativeNormError (a b : ℝ) : ℝ := max 0 (a / b - 1)

@[simp] theorem relativeNormError_nonneg (a b : ℝ) : 0 ≤ relativeNormError a b :=
  le_max_left _ _







end ErrorTransfer

section OperatorCauchySchwarz

variable {ι : Type*} {E F 𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]









end OperatorCauchySchwarz

section HilbertCoefficientEnergy

variable {ι E F 𝕜 : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]





end HilbertCoefficientEnergy

section Counts

/-- The four oriented letters of a free group on two generators. -/
abbrev Letter := Fin 4

/-- `0 ↔ 3` and `1 ↔ 2` form the two inverse pairs. -/
def inverseLetter (a : Letter) : Letter := a.rev

@[simp] theorem inverseLetter_inverse (a : Letter) :
    inverseLetter (inverseLetter a) = a := by simp [inverseLetter]



/-- Legal letters following `a`: all letters except its inverse. -/
abbrev FollowingLetter (a : Letter) := {b : Letter // b ≠ inverseLetter a}

@[simp] theorem card_followingLetter (a : Letter) :
    Fintype.card (FollowingLetter a) = 3 := by
  simp [FollowingLetter, Fintype.card_subtype_compl]

/-- A genuine reduced tail; each next letter excludes the previous inverse. -/
def ReducedTail (a : Letter) : ℕ → Type
  | 0 => Unit
  | n + 1 => Σ b : FollowingLetter a, ReducedTail b.val n

noncomputable instance reducedTailFintype (a : Letter) (n : ℕ) :
    Fintype (ReducedTail a n) := by
  induction n generalizing a with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    change Fintype (Σ b : FollowingLetter a, ReducedTail b.val n)
    letI : ∀ b : FollowingLetter a, Fintype (ReducedTail b.val n) := fun b => ih b.val
    infer_instance

/-- Exactly three choices are available for each subsequent letter. -/
@[simp] theorem card_reducedTail (a : Letter) (n : ℕ) :
    Fintype.card (ReducedTail a n) = 3 ^ n := by
  induction n generalizing a with
  | zero => simp [ReducedTail]
  | succ n ih =>
    change Fintype.card (Σ b : FollowingLetter a, ReducedTail b.val n) = _
    rw [Fintype.card_sigma]
    simp [ih, pow_succ, mul_comm]

/-- A nonempty reduced word of length `t+1` is its first letter and reduced tail. -/
abbrev ReducedWord (t : ℕ) := Σ a : Letter, ReducedTail a t








end Counts

end Nonadditivity.Linearization


