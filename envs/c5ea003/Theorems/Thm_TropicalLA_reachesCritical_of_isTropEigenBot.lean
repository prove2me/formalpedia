-- Prove2me | Theorems.Thm_TropicalLA_reachesCritical_of_isTropEigenBot
-- name    : TropicalLA.reachesCritical_of_isTropEigenBot
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:56:01.99041+00:00
-- url     : https://prove2.me/theorems/c4074547-c602-45c4-a575-761b079d1fc2
-- title:
--   Every vertex reaches a critical node: follow the tight successors until the orbit
-- statement:
--   Every vertex reaches a critical node: follow the tight successors until the orbit
--   closes up.
--
--   ```lean
--   theorem TropicalLA.reachesCritical_of_isTropEigenBot{v : ι → ℝ} (h : IsTropEigenBot A lam v) :
--       ReachesCritical A lam := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalReducible.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalReducible.lean#L84

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

theorem TropicalLA.reachesCritical_of_isTropEigenBot{v : ι → ℝ} (h : IsTropEigenBot A lam v) :
    ReachesCritical A lam := by sorry
