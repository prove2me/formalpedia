-- Prove2me | Definitions.Def_Bridges_GraphTheory_SupportCompression
-- name    : Bridges_GraphTheory_SupportCompression
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:41.44053+00:00
-- url     : https://prove2.me/theorems/61c59644-f305-432f-aeb7-a163e246066f
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_SupportCompression
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.SupportCompression`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/SupportCompression.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Sparse-Support Certificate Compression for Matroid Basis Polynomials

This file formalizes the structural principle that Lorentzian recognition
recursion trees collapse for matroid basis generating polynomials. The key
insight is that the surviving derivative branches in the recursive Lorentzian
recognition algorithm are governed not by ambient monomial counts, but by
the independent-set geometry of the underlying matroid.

## Main Definitions

* `NonzeroDerivativeLeafSet` — The set of k-element subsets contained in some
  member of a family of sets (derivative branches that survive)
* `supportCompressedLeafCount` — The cardinality of the nonzero derivative leaf set
* `activeVariableSet` — The union of all variables appearing in the support
* `activeVariableCount` — The size of the active variable set

## Main Results

* `nonzeroDerivativeLeafSet_eq_indep` — For matroid bases, surviving derivative
  leaves are exactly the independent sets of the given size
* `supportCompressedLeafCount_uniformBases` — Exact closed form: for uniform
  matroids, the quadratic leaf count equals C(n, r-2)
* `supportCompressedLeafCount_le_active_choose` — Upper bound by C(|active vars|, k)

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Murota, "Discrete Convex Analysis", SIAM, 2003
-/

open Finset BigOperators Classical

noncomputable section

namespace SupportCompression

variable {n : ℕ}

/-! ## Core Definitions -/

/-- The set of k-element subsets of `Fin n` that are contained in some member
of a given family `bases`. In the context of Lorentzian recognition, these are
the derivative branches that produce nonzero results: a multiindex α of degree k
yields a nonzero derivative of a multiaffine polynomial iff supp(α) ⊆ some
support element, which for basis generating polynomials means supp(α) is
contained in some basis. -/
def NonzeroDerivativeLeafSet (bases : Finset (Finset (Fin n))) (k : ℕ) :
    Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard k).filter fun I =>
    ∃ B ∈ bases, I ⊆ B

/-- The support-compressed leaf count: the number of k-element subsets that are
contained in some member of the family. This is the correct complexity measure
for recursive Lorentzian recognition. -/
def supportCompressedLeafCount (bases : Finset (Finset (Fin n))) (k : ℕ) : ℕ :=
  (NonzeroDerivativeLeafSet bases k).card

/-- The set of all variables (elements of `Fin n`) that appear in at least one
member of the family. -/
def activeVariableSet (bases : Finset (Finset (Fin n))) : Finset (Fin n) :=
  bases.biUnion id

/-- The number of active variables. -/
def activeVariableCount (bases : Finset (Finset (Fin n))) : ℕ :=
  (activeVariableSet bases).card

/-- The uniform basis family: all r-element subsets of `Fin n`. This corresponds
to the uniform matroid U_{r,n}. -/
def uniformBases (r : ℕ) : Finset (Finset (Fin n)) :=
  (univ : Finset (Fin n)).powersetCard r

/-- Verified algorithm: count nonzero quadratic leaves directly from support data.
This avoids symbolic differentiation entirely. -/
def countNonzeroQuadraticLeavesFromSupport
    (bases : Finset (Finset (Fin n))) (r : ℕ) : ℕ :=
  supportCompressedLeafCount bases (r - 2)

/-! ## Membership Characterization -/


/-! ## Matroid Bridge: Independence = Containment in a Base -/

/-
For a matroid M on Fin n, the set of k-element subsets contained in some
base equals the set of k-element independent sets.

This connects the combinatorial leaf set to matroid independence. In Mathlib,
`M.Indep I ↔ ∃ B, M.IsBase B ∧ I ⊆ B` is the definition.
-/

/-! ## Uniform Matroid: Exact Closed Form -/

/-
Every (r-2)-element subset of Fin n is contained in some r-element subset,
provided r ≤ n and 2 ≤ r. This is the key combinatorial fact for the uniform
matroid closed form.
-/

/-
For the uniform matroid U_{r,n}, the nonzero derivative leaf set at degree
(r-2) is the entire set of (r-2)-element subsets.
-/

/-
**Theorem 3 (Uniform Matroid Closed Form).**
For the uniform matroid U_{r,n}, the number of nonzero quadratic derivative
leaves equals C(n, r-2).
-/

/-! ## Upper Bound by Active Variable Count -/

/-
Any set in the nonzero derivative leaf set is contained in the active
variable set.
-/

/-
The nonzero derivative leaf set is contained in the powerset of the active
variable set.
-/

/-
**Theorem 4 (Support Compression Bound).**
For any family of sets, the number of k-element subsets contained in some member
is at most C(|active variables|, k).
-/

/-! ## Monotonicity Properties -/

/-
The nonzero derivative leaf set is monotone in the family of bases.
-/

/-
The leaf count is monotone in the family of bases.
-/

/-! ## Verified Algorithm Correctness -/


/-! ## Empty and Trivial Cases -/

/-
The leaf set of an empty family is empty.
-/

/-
The leaf count of an empty family is zero.
-/

/-
For k = 0, the leaf set contains exactly the empty set (if the family
is nonempty).
-/

/-
For k = 0 and nonempty family, the leaf count is 1.
-/

/-! ## Leaf Count Bounded by Ambient Count -/

/-
The support-compressed leaf count is always at most C(n, k),
the ambient worst-case count.
-/

end SupportCompression


