-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
-- name    : Algebra_TropicalLinearAlgebra_TropicalIrreducible
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:29:58.455985+00:00
-- url     : https://prove2.me/theorems/f76e4c06-e520-430a-a58b-b0caae36b2bb
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_TropicalIrreducible
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.TropicalIrreducible`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/TropicalIrreducible.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
/-
# Tropical Perron–Frobenius with `−∞` entries

This file settles conjecture **C4** of `FUTURE_DIRECTIONS.md`.  Matrices are now
allowed genuine tropical zeros `⊥ = −∞`, i.e. `A : Matrix ι ι (WithBot ℝ)`, and an
*eigenvector* is still required to be **finite** (`v : ι → ℝ`):

  `IsTropEigenBot A lam v : ∀ i, ⨆ j (A i j + v j) = lam + v i`   (sup in `WithBot ℝ`).

Main results:

* `exists_tropEigenBot_of_stronglyConnected` — **existence**: if the support digraph
  `Supp A` (the pairs with `A i j ≠ ⊥`) is strongly connected, then `A` has a tropical
  eigenvalue with a finite eigenvector.  The proof is a *perturbation* argument: replace
  every `⊥` by a finite but very negative penalty, apply the finite-entry
  Perron–Frobenius theorem `exists_tropEigen`, normalise the eigenvector to have maximum
  `0`, and show — using short support walks — that its entries stay in a fixed compact
  interval that does not depend on the penalty.  Hence for a large enough penalty no
  optimal row entry can use a `⊥` position, and the eigenvector of the perturbed matrix
  is an eigenvector of `A` itself.
* `IsTropEigenBot.isGreatest_suppCycleMean` — the eigenvalue is exactly the maximum mean
  weight of a closed walk in the support digraph, and hence
* `tropEigenvalueBot_unique` — **uniqueness** of the eigenvalue, *without* any
  irreducibility hypothesis.
* `not_stronglyConnected_of_isTropEigenBot_false` — the converse half of C4 is **false**:
  the `2 × 2` matrix `diag(0, 0)` (with `⊥` off the diagonal) has the finite eigenvector
  `(0,0)` although its support digraph is not strongly connected.  So strong connectivity
  is sufficient but not necessary, and C4 must be weakened to the implication proved here.

Auxiliary combinatorics, of independent interest:

* `exists_short_supp_walk` — in a strongly connected digraph on `n` vertices any two
  vertices are joined by a walk of length between `1` and `n` (proved by excising
  repeated vertices);
* `IsTropEigen.pathWeight_le` — the telescoping bound `w(p) + v(p m) ≤ m·lam + v(p 0)`
  for a finite-entry eigenpair, which generalises `IsTropEigen.cycle_le`.
-/

namespace TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Matrices over `WithBot ℝ`: support, walks, eigenpairs -/

section Defs

variable (A : Matrix ι ι (WithBot ℝ))

/-- The **support digraph** of a tropical matrix: `i → j` is an edge when `A i j ≠ ⊥`. -/
def Supp (i j : ι) : Prop := A i j ≠ ⊥

/-- `A` is **irreducible** when its support digraph is strongly connected: any two
vertices (including a vertex and itself) are joined by a walk of positive length. -/
def StronglyConnected : Prop := ∀ i j, Relation.TransGen (Supp A) i j

/-- The finite part of a tropical matrix (`⊥` entries are sent to `0`; the value there
is irrelevant, all statements below only use `finPart` on the support). -/
noncomputable def finPart : Matrix ι ι ℝ := fun i j => (A i j).unbotD 0

/-- A walk all of whose steps are edges of the support digraph. -/
def IsSuppWalk (p : ℕ → ι) (m : ℕ) : Prop := ∀ t < m, Supp A (p t) (p (t + 1))

/-- Tropical matrix–vector product with `⊥` allowed in the matrix and a finite vector. -/
noncomputable def tmulVecBot (v : ι → ℝ) : ι → WithBot ℝ :=
  fun i => Finset.univ.sup fun j => A i j + (v j : WithBot ℝ)

/-- `lam` is a tropical eigenvalue of `A` with **finite** eigenvector `v`. -/
def IsTropEigenBot (lam : ℝ) (v : ι → ℝ) : Prop :=
  ∀ i, tmulVecBot A v i = ((lam + v i : ℝ) : WithBot ℝ)

end Defs

variable {A : Matrix ι ι (WithBot ℝ)}



namespace IsTropEigenBot

variable {lam : ℝ} {v : ι → ℝ}




end IsTropEigenBot

/-! ## Short walks in a strongly connected support digraph -/




/-! ## Telescoping along a walk, for finite-entry eigenpairs -/



/-! ## The perturbed matrix -/

section Perturb

variable (A)

/-- The smallest entry of the finite part (over *all* index pairs). -/
noncomputable def entryMin : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun p : ι × ι => finPart A p.1 p.2)

/-- The largest entry of the finite part (over *all* index pairs). -/
noncomputable def entryMax : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : ι × ι => finPart A p.1 p.2)

/-- The spread bound `n · (max − min)`; the normalised eigenvector of the perturbed
matrix will be shown to lie in `[-spreadBound, 0]`. -/
noncomputable def spreadBound : ℝ := Fintype.card ι * (entryMax A - entryMin A)

/-- The penalty replacing `⊥`: chosen so large that no optimal choice can use it. -/
noncomputable def penalty : ℝ := spreadBound A - entryMin A + 1

/-- The perturbed (finite-entry) matrix: every `⊥` is replaced by `-penalty A`. -/
noncomputable def approx : Matrix ι ι ℝ := fun i j => (A i j).unbotD (-penalty A)

variable {A}














end Perturb

/-! ## Existence of an eigenvector with `⊥` entries -/


/-! ## The eigenvalue is the maximum support cycle mean -/

namespace IsTropEigenBot

variable {lam : ℝ} {v : ι → ℝ}




end IsTropEigenBot



/-! ## The converse of C4 is false -/

/-- The `2 × 2` diagonal matrix `diag(0,0)` with `⊥` off the diagonal. -/
noncomputable def diagBotExample : Matrix (Fin 2) (Fin 2) (WithBot ℝ) :=
  fun i j => if i = j then ((0 : ℝ) : WithBot ℝ) else ⊥




end TropicalLA


