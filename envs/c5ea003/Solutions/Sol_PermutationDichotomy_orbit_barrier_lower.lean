-- Prove2me | solution 1 for PermutationDichotomy.orbit_barrier_lower
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:09:43.608289+00:00
-- url     : https://prove2.me/submissions/e378edf5-3ebb-42cc-bef2-2e1a2745a84d

import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_PermutationDichotomy

open scoped BigOperators
open PermutationDichotomy

set_option autoImplicit false

/- Ported from paulklemstine/Lean, commit 53c2925a02,
   Catalog/MachineLearning/TransformerUniversality/PermutationDichotomy.lean.
   The upstream proof is retained; target typeclass binders are declared once. -/
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] (g : Seq ι κ → ℝ) (x : Seq ι κ)
    {p : Seq ι κ → ℝ} (hp : Invariant p) :
    ((Finset.univ.sup' Finset.univ_nonempty fun σ : Equiv.Perm ι => g (permAct σ x))
        - Finset.univ.inf' Finset.univ_nonempty fun σ : Equiv.Perm ι => g (permAct σ x)) / 2
      ≤ Finset.univ.sup' Finset.univ_nonempty
          fun σ : Equiv.Perm ι => |p (permAct σ x) - g (permAct σ x)| := by
  classical
  obtain ⟨sM, -, hsM⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Equiv.Perm ι))
    (fun σ : Equiv.Perm ι => g (permAct σ x))
  obtain ⟨sm, -, hsm⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Equiv.Perm ι))
    (fun σ : Equiv.Perm ι => g (permAct σ x))
  have hM : |p (permAct sM x) - g (permAct sM x)|
      ≤ Finset.univ.sup' Finset.univ_nonempty
          fun σ : Equiv.Perm ι => |p (permAct σ x) - g (permAct σ x)| :=
    Finset.le_sup' (fun σ : Equiv.Perm ι => |p (permAct σ x) - g (permAct σ x)|)
      (Finset.mem_univ sM)
  have hm : |p (permAct sm x) - g (permAct sm x)|
      ≤ Finset.univ.sup' Finset.univ_nonempty
          fun σ : Equiv.Perm ι => |p (permAct σ x) - g (permAct σ x)| :=
    Finset.le_sup' (fun σ : Equiv.Perm ι => |p (permAct σ x) - g (permAct σ x)|)
      (Finset.mem_univ sm)
  have e1 : p (permAct sM x) = p x := hp sM x
  have e2 : p (permAct sm x) = p x := hp sm x
  have hconst : p (permAct sM x) = p (permAct sm x) := by rw [e1, e2]
  have h1 : g (permAct sM x) - p (permAct sM x) ≤ |p (permAct sM x) - g (permAct sM x)| := by
    rw [abs_sub_comm]; exact le_abs_self _
  have h2 : p (permAct sm x) - g (permAct sm x) ≤ |p (permAct sm x) - g (permAct sm x)| :=
    le_abs_self _
  rw [hsM, hsm]
  linarith
