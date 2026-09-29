-- Prove2me | Theorems.Thm_TropicalLA_critPotential_nonneg_of_critical
-- name    : TropicalLA.critPotential_nonneg_of_critical
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:26:05.214464+00:00
-- url     : https://prove2.me/theorems/38330821-7d6e-4ead-ba2f-4086ecde4b3f
-- title:
--   A critical node has nonnegative critical potential (its own critical cycle).
-- statement:
--   A critical node has nonnegative critical potential (its own critical cycle).
--
--   ```lean
--   theorem TropicalLA.critPotential_nonneg_of_critical{c₀ : ι} (hc₀ : IsCriticalNode A lam c₀) {c : ι}
--       (hc : IsCriticalNode A lam c) : 0 ≤ critPotential A lam c₀ c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalReducible.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalReducible.lean#L419

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalReducible.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalReducible
/-
# The general (reducible) tropical Perron–Frobenius theorem

`TropicalIrreducible.lean` proves that an **irreducible** max-plus matrix with `⊥ = −∞`
entries has a finite eigenvector, and refutes the converse.  This file gives the exact
characterisation, with no connectivity hypothesis at all:

> `A : Matrix ι ι (WithBot ℝ)` has a finite eigenvector for the eigenvalue `lam`
> **iff**
> (a) every closed walk in the support digraph has mean weight at most `lam`
>     (`AllSuppCyclesLe`), and
> (b) every vertex is joined by a support walk to a vertex lying on a closed support walk
>     of mean weight exactly `lam` — a *critical node* (`ReachesCritical`).

This is `tropEigenBot_iff_criticalReachable`.  It contains the irreducible case (there
every vertex reaches every other, and a critical cycle exists) and explains the
counterexample `diag(0,0)` of the previous file (each of the two vertices carries its own
critical loop, so (b) holds even though the digraph is disconnected).

The construction of the eigenvector is a *critical potential*: `v j` is the largest weight
of a normalised support walk from `j` to a critical node.  Two devices make it usable in
Lean:

* walks are cut down to length `≤ n = |ι|` by `exists_short_suppWalk_ge`, an excision
  lemma that preserves the support and does not decrease the weight (the excised closed
  sub-walks have nonpositive normalised weight by (a));
* the maximum is taken over the finite index set `range n ×ˢ univ` of the *penalised*
  matrix `normApprox A lam` (each `⊥` is replaced by a large negative number).  A separate
  estimate shows the penalty is so large that the optimal walk never uses a `⊥` position,
  so the penalised optimum is genuinely a maximum over support walks.
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Critical nodes and the two conditions -/


variable (A : Matrix ι ι (WithBot ℝ)) (lam : ℝ)





variable {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ}

/-! ## Necessity of the two conditions -/




/-! ## Excision preserving the support -/


/-! ## The penalised normalised matrix -/


variable (A lam)




variable {A lam}












/-! ## The critical potential -/






/-! ## Sufficiency of the two conditions -/


variable (hle : AllSuppCyclesLe A lam) (hreach : ReachesCritical A lam)






include hle in

theorem TropicalLA.critPotential_nonneg_of_critical{c₀ : ι} (hc₀ : IsCriticalNode A lam c₀) {c : ι}
    (hc : IsCriticalNode A lam c) : 0 ≤ critPotential A lam c₀ c := by sorry
