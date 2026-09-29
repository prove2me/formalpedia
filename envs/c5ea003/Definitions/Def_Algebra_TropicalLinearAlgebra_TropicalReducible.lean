-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalReducible
-- name    : Algebra_TropicalLinearAlgebra_TropicalReducible
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:30:45.380538+00:00
-- url     : https://prove2.me/theorems/a55bd342-5893-4f16-8e50-386595b31cf3
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_TropicalReducible
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.TropicalReducible`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/TropicalReducible.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
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

namespace TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Critical nodes and the two conditions -/

section Defs

variable (A : Matrix ι ι (WithBot ℝ)) (lam : ℝ)

/-- A **critical node**: a vertex lying on a closed support walk of mean weight `lam`. -/
def IsCriticalNode (c : ι) : Prop :=
  ∃ (m : ℕ) (p : ℕ → ι), 0 < m ∧ p 0 = c ∧ p m = c ∧ IsSuppWalk A p m ∧
    pathWeight (finPart A) p m = m * lam

/-- Condition (a): no closed support walk beats the mean `lam`. -/
def AllSuppCyclesLe : Prop :=
  ∀ (m : ℕ) (p : ℕ → ι), IsSuppWalk A p m → p m = p 0 → pathWeight (finPart A) p m ≤ m * lam

/-- Condition (b): every vertex has access to the critical graph. -/
def ReachesCritical : Prop :=
  ∀ i, ∃ (m : ℕ) (p : ℕ → ι), 0 < m ∧ p 0 = i ∧ IsSuppWalk A p m ∧ IsCriticalNode A lam (p m)

end Defs

variable {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ}

/-! ## Necessity of the two conditions -/




/-! ## Excision preserving the support -/


/-! ## The penalised normalised matrix -/

section Penalty

variable (A lam)

/-- A crude bound on all the data of `(A, lam)`, at least `1`. -/
noncomputable def spreadAbs : ℝ := |entryMax A| + |entryMin A| + 2 * |lam| + 1

/-- The penalty replacing `⊥` in the normalised matrix. -/
noncomputable def penaltyN : ℝ := 2 * Fintype.card ι * spreadAbs A lam + 1

open Classical in
/-- The normalised matrix `A − lam` with `⊥` replaced by a large negative penalty. -/
noncomputable def normApprox : Matrix ι ι ℝ :=
  fun i j => if A i j = ⊥ then -penaltyN A lam else finPart A i j - lam

variable {A lam}











end Penalty

/-! ## The critical potential -/

section Potential

open Classical in
/-- `critPotential A lam c₀ j` is the maximal weight, in the penalised normalised matrix,
of a walk of length between `1` and `n` from `j` to a critical node (`c₀` is a default
critical node used to keep the index set rectangular). -/
noncomputable def critPotential (A : Matrix ι ι (WithBot ℝ)) (lam : ℝ) (c₀ j : ι) : ℝ :=
  ((Finset.range (Fintype.card ι)) ×ˢ (Finset.univ : Finset ι)).sup' cycleIndex_nonempty
    (fun q => tpow (normApprox A lam) q.1 j (if IsCriticalNode A lam q.2 then q.2 else c₀))



end Potential

/-! ## Sufficiency of the two conditions -/

section Sufficiency

variable (hle : AllSuppCyclesLe A lam) (hreach : ReachesCritical A lam)









end Sufficiency


/-! ## A worked reducible example

The general theorem genuinely covers matrices outside the reach of the irreducible one:
`A = [[0, ⊥], [5, ⊥]]` has the sink `0` as its only cycle, so vertex `1` never returns to
itself, yet every vertex reaches the critical loop at `0`. -/

noncomputable def sinkExample : Matrix (Fin 2) (Fin 2) (WithBot ℝ) :=
  fun i j => if j = 0 then (((if i = 0 then 0 else 5 : ℝ)) : WithBot ℝ) else ⊥








end TropicalLA


