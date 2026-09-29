-- Prove2me | Theorems.Thm_ChebotarevGeodesic_prime_geodesic_of_chebotarev
-- name    : ChebotarevGeodesic.prime_geodesic_of_chebotarev
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:20:16.400573+00:00
-- url     : https://prove2.me/theorems/4ec6a3b4-a303-4fc8-82b3-2be060a2298e
-- title:
--   Chebotarev â¹ prime geodesic theorem.
-- statement:
--   **Chebotarev â¹ prime geodesic theorem.**  If for every conjugacy class `C` of the (finite)
--   Galois group `G` of the covering the class-counting function `piC C` satisfies
--   `piC C (x) = (|C|/|G|) Â· li(x) + O(x^{Î¸+Îµ})`, then the total counting function
--   `â_C piC C` satisfies `Ï(x) = li(x) + O(x^{Î¸+Îµ})`: the prime geodesic theorem with the
--   same exponent.  In the paper this is the deduction of the prime geodesic theorem with
--   exponent `25/36 + Îµ` from the Chebotarev geodesic theorem with exponent `25/36 + Îµ`.
--
--   ```lean
--   theorem ChebotarevGeodesic.prime_geodesic_of_chebotarev(G : Type*) [Group G] [Fintype G] [DecidableEq G]
--       [Fintype (ConjClasses G)] (piC : ConjClasses G → ℝ → ℝ) (li : ℝ → ℝ) (θ : ℝ)
--       (h : ∀ C, HasErrorExponent (piC C) (fun x => classDensity G C * li x) θ) :
--       HasErrorExponent (fun x => ∑ C : ConjClasses G, piC C x) li θ := by sorry
--   /-! ## Qualitative consequence: every class is hit infinitely often -/
--
--
--   /-! ## The numerical record chain -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesic.lean#L237

-- Thm stub generated from Shared/ChebotarevGeodesic.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
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

open ChebotarevGeodesic

/-! ## The exponent calculus -/


variable {π π₁ π₂ M M₁ M₂ : ℝ → ℝ} {θ θ' : ℝ}








/-! ## Reduction of the non-split case to the split case:
an invertible linear transform of counting functions -/



/-! ## Conjugacy class densities in a finite group -/


variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]






/-! ## From the Chebotarev geodesic theorem to the prime geodesic theorem -/

open scoped Classical in

theorem ChebotarevGeodesic.prime_geodesic_of_chebotarev(G : Type*) [Group G] [Fintype G] [DecidableEq G]
    [Fintype (ConjClasses G)] (piC : ConjClasses G → ℝ → ℝ) (li : ℝ → ℝ) (θ : ℝ)
    (h : ∀ C, HasErrorExponent (piC C) (fun x => classDensity G C * li x) θ) :
    HasErrorExponent (fun x => ∑ C : ConjClasses G, piC C x) li θ := by sorry
