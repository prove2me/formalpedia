-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_binary_orbit_intersection_iff
-- name    : Couret.STROBO2TORS.recoh_binary_orbit_intersection_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:05.750203+00:00
-- url     : https://prove2.me/theorems/569cfdc0-39cc-4826-bd9f-591ca7d8f27c
-- title:
--   Binary probe orbits intersect exactly up to coordinate signs
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Let $B=(\chi_j)_{j\in J}$ and let $e:H\simeq(J\to\mathbb F_2)$ be an additive equivalence with $\chi_j(u)=(-1)^{e(u)_j}$. For supports $S,T$, assume every $P_{\chi_j}(S)\ne0$. Then $$\exists u,v\in H,\ \forall j,\ P_{\chi_j}(S+u)=P_{\chi_j}(T+v)\iff\forall j,\ P_{\chi_j}(S)=\pm P_{\chi_j}(T).$$ Each coordinate may choose its own sign.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCanonicalOverlap.lean, lines 45–78; source file SHA-256 34c58356d945f0f3efe34a028d955ccf56a0259547dabde0e382eaaeb03b7fe5; theorem Couret.STROBO2TORS.recoh_binary_orbit_intersection_iff

import Aesop
import Definitions.Def_Couret_RecohCanonicalOverlap_0d3ff2cb7fda
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_recovered_sign_bit_sound
import Definitions.Def_Couret_RecohCanonicalCoefficients_7eb0bfadc07d
import Definitions.Def_Couret_RecohParityDedupTransport_fd9d6ec554ae

set_option autoImplicit false

/-!
Literal canonical coefficient comparisons and the binary overlap filter.

This module proves the typed mathematical meaning of Python v0.2's
`_two_overlaps`.  It does not formalize Python execution, tuple/list parsing,
the implementation of `combinations`, exceptions, or JSON serialization.
-/

namespace Couret.STROBO2TORS

section SignOrbits

variable {G J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2

theorem recoh_binary_orbit_intersection_iff
    (bank : J → AddChar G ℂ) (e : H₂ ≃+ (J → ZMod 2))
    (hcoord : ∀ (u : H₂) (i : J),
      bank i (u : G) = if e u i = 0 then 1 else -1)
    (B C : Finset G) (hnonzero : ∀ i, recohSupportProbe (bank i) B ≠ 0) :
    (∃ u v : H₂, ∀ i,
      recohSupportProbe (bank i) (translateSupport B (u : G)) =
        recohSupportProbe (bank i) (translateSupport C (v : G))) ↔
    (∀ i, recohSupportProbe (bank i) B = recohSupportProbe (bank i) C ∨
      recohSupportProbe (bank i) B = -recohSupportProbe (bank i) C) := by sorry


end SignOrbits

section LiteralComparison

variable {I : Type*} [Fintype I]





end LiteralComparison

section IndexedPairs

variable {A : Type*}









end IndexedPairs

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]























end Cyclic

end Couret.STROBO2TORS
