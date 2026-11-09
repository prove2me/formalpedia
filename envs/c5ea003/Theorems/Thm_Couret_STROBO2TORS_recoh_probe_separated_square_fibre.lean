-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_probe_separated_square_fibre
-- name    : Couret.STROBO2TORS.recoh_probe_separated_square_fibre
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:05.037789+00:00
-- url     : https://prove2.me/theorems/1938932a-1316-4b85-b2f0-ce8ff47f8184
-- title:
--   Amplitude and orbit-separator contracts give quantitative fibre separation
-- statement:
--   Let $G$ be an abelian group, $P_\chi(A)=\sum_{x\in A}\chi(x)$, $R_A(z)$ the ordered pair-sum count, $F(A)$ the full fibre among three-element supports, and $H=G[2]$. A bank is $\delta$-separated on a candidate set when every two distinct candidates have at least one reading whose distance is at least $\delta$. Assume $G$ finite. Let banks $\alpha_i,\beta_j$ be indexed by any types, and let $b\in\mathbb R$ with $b\le\sqrt3$. Suppose $|P_{\alpha_i}(T)|\ge b$ for every $T\in F(A)$ and every $i$; the common $\alpha$ kernel on $H$ is trivial; every $\beta_j$ is trivial on $H$; and equality of all $\beta$ readings for two fibre members implies they are $H$-translates. Then
--
--   $$\alpha\sqcup\beta\text{ is }2b\text{-separated on }F(A).$$
--
--   No positivity assumption on $b$ is present.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohExceptionalStability.lean#L164-L193, lines 164–193; source file SHA-256 788e929f7e526870f55ea3a771c8f7f5dc647bcd18b0afb61c80f3eaf4f4c947; theorem Couret.STROBO2TORS.recoh_probe_separated_square_fibre

import Aesop
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_exceptional_probe_distance_of_ne
import Theorems.Thm_Couret_STROBO2TORS_recoh_ordinary_probe_distance
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15

set_option autoImplicit false

/-!
Exact separation constants in the exceptional normal form.  Binary probes
have amplitudes one or three, and a detecting ternary probe separates the
two orbits by exactly twice the square root of three.  The two-torsion pair
inside the normal form supplies a matching universal upper bound of two.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] [DecidableEq G]





variable [Fintype G]

theorem recoh_probe_separated_square_fibre
    {I J : Type*} (bank2 : I → AddChar G ℂ) (bank3 : J → AddChar G ℂ)
    (S : Finset G) (a : ℝ) (ha : a ≤ Real.sqrt 3)
    (hamp : ∀ T ∈ squareFibre S, ∀ i, a ≤ ‖recohSupportProbe (bank2 i) T‖)
    (hsep2 : ∀ u : G, u + u = 0 → (∀ i, bank2 i u = 1) → u = 0)
    (htrivial : ∀ j, ∀ u : G, u + u = 0 → bank3 j u = 1)
    (horbits : ∀ B ∈ squareFibre S, ∀ C ∈ squareFibre S,
      (∀ j, recohSupportProbe (bank3 j) B = recohSupportProbe (bank3 j) C) →
        OrdinaryPartner B C) :
    RecohProbeSeparated (Sum.elim bank2 bank3) (squareFibre S) (2 * a) := by sorry








end Couret.STROBO2TORS
