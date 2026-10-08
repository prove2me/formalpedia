-- Prove2me | Theorems.Thm_GoldbachDirichletZeros_compact_occurrence_enumeration
-- name    : GoldbachDirichletZeros.compact_occurrence_enumeration
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T05:16:05.619263+00:00
-- url     : https://prove2.me/theorems/9d4fb358-c442-42f8-a340-4d537f3cf7bd
-- title:
--   Exact multiplicity-preserving enumeration of compact Dirichlet zero collections
-- statement:
--   Let $N\ge 1$, let $K\subseteq\mathbb C$ be compact, and let $\chi$ range over all complex Dirichlet characters modulo $N$. Write
--   $$
--   Z_\chi(K)=\{\rho\in K:\rho\ne1,\ L(\chi,\rho)=0\},\qquad
--   m_\chi(\rho)=\operatorname{ord}_\rho L(\chi,\cdot).
--   $$
--   Each set $Z_\chi(K)$ is finite. Every zero away from $1$ has finite, strictly positive analytic multiplicity; its natural-number multiplicity represents its analytic order exactly.
--
--   There are a natural number $n$ and a bijection from the tagged occurrence collection
--   $$
--   \mathcal O_N(K)=\{(\chi,\rho,j):\rho\in Z_\chi(K),\ 0\le j<m_\chi(\rho)\}
--   $$
--   to $\{0,\ldots,n-1\}$. If $a_i$ denotes the inverse image of $i$ under this bijection, then
--   $$
--   n=\sum_\chi\sum_{\rho\in Z_\chi(K)}m_\chi(\rho),\qquad
--   \sum_{i=0}^{n-1}w(\chi(a_i),\rho(a_i))
--   =\sum_\chi\sum_{\rho\in Z_\chi(K)}m_\chi(\rho)w(\chi,\rho)
--   $$
--   for every real-valued weight $w$ on characters and complex points.
--
--   This interface preserves multiplicities and character labels when passing from actual Dirichlet zeros to finite detector sums. It applies to the principal character too, excludes the possible pole at $1$, and allows empty collections. It supplies no numerical zero-density estimate or uniform bound as $N$ varies.
--
--   **Formalization Note** The finite zero-set instances and the bijection are existentially supplied. Multiplicity is the natural-number conversion of the analytic order, accompanied by a proof that this conversion loses no information.
-- source:
--   Integration corollary of Mathlib at revision 777aaa6, not a new zero-density result: https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean (differentiable_LFunction, differentiable_LFunctionTrivChar₁, LFunctionTrivChar₁_apply_one_ne_zero); https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/NumberTheory/LSeries/Nonvanishing.lean (LFunction_apply_one_ne_zero); https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/Analysis/Analytic/Order.lean (preimage_zero_mem_codiscreteWithin, analyticOrderAt_ne_top_of_isPreconnected, analyticOrderAt_mul); https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/Data/Fintype/BigOperators.lean (card_sigma, sum_sigma).

import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

open Complex Set Filter Topology
open scoped BigOperators
set_option autoImplicit false

theorem GoldbachDirichletZeros.compact_occurrence_enumeration (N : ℕ) [NeZero N] (K : Set ℂ) (hK : IsCompact K) :
    (∀ χ : DirichletCharacter ℂ N,
      (K ∩ {s | s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0}).Finite) ∧
    (∀ (χ : DirichletCharacter ℂ N) (s : ℂ), s ≠ 1 →
      DirichletCharacter.LFunction χ s = 0 →
      ((analyticOrderAt (DirichletCharacter.LFunction χ) s).toNat : ENat) =
        analyticOrderAt (DirichletCharacter.LFunction χ) s ∧
      0 < (analyticOrderAt (DirichletCharacter.LFunction χ) s).toNat) ∧
    ∃ iz : ∀ χ : DirichletCharacter ℂ N,
        Fintype {s : ℂ // s ∈ K ∧ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0},
      letI (χ : DirichletCharacter ℂ N) := iz χ
      ∃ (n : ℕ) (e : (Σ χ : DirichletCharacter ℂ N,
        Σ z : {s : ℂ // s ∈ K ∧ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0},
          Fin ((analyticOrderAt (DirichletCharacter.LFunction χ) z.val).toNat)) ≃ Fin n),
        n = ∑ χ : DirichletCharacter ℂ N,
          ∑ z : {s : ℂ // s ∈ K ∧ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0},
            (analyticOrderAt (DirichletCharacter.LFunction χ) z.val).toNat ∧
        ∀ w : DirichletCharacter ℂ N → ℂ → ℝ,
          (∑ i : Fin n, w (e.symm i).1 (e.symm i).2.1.val) =
          ∑ χ : DirichletCharacter ℂ N,
            ∑ z : {s : ℂ // s ∈ K ∧ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0},
              ((analyticOrderAt (DirichletCharacter.LFunction χ) z.val).toNat : ℝ) *
                w χ z.val := by sorry
