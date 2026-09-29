-- Prove2me | solution 1 for PermutationDichotomy.orbit_barrier_attained
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:09:56.927732+00:00
-- url     : https://prove2.me/submissions/10a42434-cd59-41ee-8267-ee1fe32c757f

import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_PermutationDichotomy

open scoped BigOperators
open PermutationDichotomy

set_option autoImplicit false

/- Ported from paulklemstine/Lean, commit 53c2925a02,
   Catalog/MachineLearning/TransformerUniversality/PermutationDichotomy.lean.
   The upstream proof is retained; target typeclass binders are declared once. -/
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] (g : Seq ι κ → ℝ) (x : Seq ι κ) :
    ∃ p : Seq ι κ → ℝ, Invariant p ∧ ∀ σ : Equiv.Perm ι,
      |p (permAct σ x) - g (permAct σ x)|
        ≤ ((Finset.univ.sup' Finset.univ_nonempty fun τ : Equiv.Perm ι => g (permAct τ x))
            - Finset.univ.inf' Finset.univ_nonempty
                fun τ : Equiv.Perm ι => g (permAct τ x)) / 2 := by
  classical
  set M := Finset.univ.sup' Finset.univ_nonempty fun τ : Equiv.Perm ι => g (permAct τ x) with hMdef
  set m := Finset.univ.inf' Finset.univ_nonempty fun τ : Equiv.Perm ι => g (permAct τ x) with hmdef
  refine ⟨fun _ => (M + m) / 2, fun _ _ => rfl, ?_⟩
  intro σ
  have hle : g (permAct σ x) ≤ M := by
    rw [hMdef]
    exact Finset.le_sup' (fun τ : Equiv.Perm ι => g (permAct τ x)) (Finset.mem_univ σ)
  have hge : m ≤ g (permAct σ x) := by
    rw [hmdef]
    exact Finset.inf'_le (fun τ : Equiv.Perm ι => g (permAct τ x)) (Finset.mem_univ σ)
  rw [abs_le]
  constructor <;> linarith
