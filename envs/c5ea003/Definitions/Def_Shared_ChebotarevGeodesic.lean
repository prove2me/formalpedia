-- Prove2me | Definitions.Def_Shared_ChebotarevGeodesic
-- name    : Shared_ChebotarevGeodesic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:13.496398+00:00
-- url     : https://prove2.me/theorems/c47eae15-99c6-4a99-9ff5-5de89327dd88
-- title:
--   Aether Catalog definitions — Shared_ChebotarevGeodesic
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ChebotarevGeodesic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ChebotarevGeodesic.lean by skeleton subtraction
import Mathlib
/-
# A Formal Framework for the Chebotarev Geodesic Theorem (non-split case)

Motivated by the paper *"Chebotarev geodesic theorem: non-split case"*, which proves the
geodesic analogue of the Chebotarev density theorem for congruence subgroups of indefinite
quaternion orders with error exponent `25/36 + ε`, and deduces from it the prime geodesic
theorem with the same exponent.

The analytic input of such papers (spectral theory of the Laplacian, Kuznetsov/Selberg trace
formulae, bounds for exponential sums) is far outside the reach of a formal library today.
What *is* formalizable — and what is the actual logical skeleton of the deduction
"Chebotarev with exponent θ ⟹ prime geodesic theorem with exponent θ" — is the calculus of
**error exponents** together with the **group-theoretic bookkeeping** of conjugacy classes and
the **linear-algebraic character/orthogonality reduction** which converts the non-split problem
into the split one.

This file develops that skeleton rigorously:

* `HasErrorExponent π M θ` : `π x = M x + O(x^{θ+ε})` for every `ε > 0`;
* the exponent calculus: monotonicity, sums, scalar multiples, finite sums, finite
  linear combinations, and perturbation by lower-order terms;
* `exponent_of_inverse_transform`: if an *invertible* linear transform (a "character table")
  of a family of counting functions satisfies the estimate, then so does every member of the
  family.  This is the abstract form of the reduction of the non-split case to the split case;
* `classDensity` for a finite group, `sum_classDensity`, and
  `prime_geodesic_of_chebotarev`: summing the Chebotarev asymptotics over all conjugacy
  classes yields the prime geodesic theorem with the same exponent;
* `tendsto_atTop_of_hasErrorExponent`: an error exponent smaller than the growth exponent of
  the main term forces the qualitative Chebotarev statement (each class is hit infinitely
  often);
* the numerical record chain `25/36 < 71/102 < 7/10 < 35/48 < 3/4` and its consequences.
-/


open Finset Filter
open scoped Topology

namespace ChebotarevGeodesic

/-! ## The exponent calculus -/

/-- `HasErrorExponent π M θ` says that the counting function `π` is approximated by the main
term `M` with error `O(x^{θ+ε})` for every `ε > 0`.  This is exactly the shape of the
conclusion of a prime geodesic / Chebotarev geodesic theorem "with exponent `θ + ε`". -/
def HasErrorExponent (π M : ℝ → ℝ) (θ : ℝ) : Prop :=
  ∀ ε > 0, ∃ C > 0, ∃ X ≥ (1 : ℝ), ∀ x ≥ X, |π x - M x| ≤ C * x ^ (θ + ε)

variable {π π₁ π₂ M M₁ M₂ : ℝ → ℝ} {θ θ' : ℝ}








/-! ## Reduction of the non-split case to the split case:
an invertible linear transform of counting functions -/



/-! ## Conjugacy class densities in a finite group -/

section Densities

variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]

open scoped Classical in
/-- The number of elements of `G` lying in the conjugacy class `C`. -/
noncomputable def classSize [Fintype (ConjClasses G)] (C : ConjClasses G) : ℕ :=
  (Finset.univ.filter (fun g : G => ConjClasses.mk g = C)).card

open scoped Classical in
/-- The Chebotarev density attached to a conjugacy class: `|C| / |G|`. -/
noncomputable def classDensity [Fintype (ConjClasses G)] (C : ConjClasses G) : ℝ :=
  (classSize G C : ℝ) / (Fintype.card G : ℝ)



end Densities

/-! ## From the Chebotarev geodesic theorem to the prime geodesic theorem -/


/-! ## Qualitative consequence: every class is hit infinitely often -/


/-! ## The numerical record chain -/




end ChebotarevGeodesic


