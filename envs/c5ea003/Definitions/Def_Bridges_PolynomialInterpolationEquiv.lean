-- Prove2me | Definitions.Def_Bridges_PolynomialInterpolationEquiv
-- name    : Bridges_PolynomialInterpolationEquiv
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:22.076056+00:00
-- url     : https://prove2.me/theorems/6f82e367-2fb2-4231-bede-98495831897e
-- title:
--   Aether Catalog definitions — Bridges_PolynomialInterpolationEquiv
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PolynomialInterpolationEquiv`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PolynomialInterpolationEquiv.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026. All rights reserved.

# Polynomial Interpolation as a Linear Equivalence

This file proves that evaluation at `n+1` distinct field points gives a canonical
`K`-linear equivalence between bounded-degree polynomials and function values,
with `Lagrange.interpolate` as the explicit inverse.

## Main Results

* `evalOnNodesLinearEquiv` — the certified `LinearEquiv` between
  `Polynomial.degreeLT K (n+1)` and `Fin (n+1) → K`.
* `natDegree_interpolate_le` — Lagrange interpolation produces polynomials of
  degree `< n+1` when interpolating on `n+1` distinct nodes.
* `eval_interp_eq_id` — evaluation of the interpolation recovers the data.
* `interp_eval_eq_id` — interpolation of evaluated bounded-degree polynomial
  recovers the polynomial, by uniqueness.

## Mathematical Significance

This theorem is simultaneously:
- a **Vandermonde invertibility** result,
- an **exact decoder** for Reed–Solomon evaluation codes,
- a **finite sheaf gluing** theorem on a discrete site,
- a **symbolic regression identifiability** result over fields.

It upgrades interpolation from an existence lemma to a certified algebraic
isomorphism, providing a reusable finite-data reconstruction primitive.
-/


open Polynomial Lagrange Finset

variable {K : Type*} [Field K] {n : ℕ}

namespace PolynomialInterpolation

/-! ## Degree bound for Lagrange interpolation -/

/-
Lagrange interpolation on `n+1` distinct nodes produces a polynomial of
`degree < n+1`, hence in `degreeLT K (n+1)`.
-/
theorem degree_interpolate_lt_of_injective (v : Fin (n + 1) → K)
    (hv : Function.Injective v) (f : Fin (n + 1) → K) :
    ((Lagrange.interpolate Finset.univ v) f).degree < ↑(n + 1) := by
  -- Apply the Lagrange degree bound lemma with the set of all nodes and the injectivity hypothesis.
  have h_deg : (interpolate (Finset.univ : Finset (Fin (n + 1))) v f).degree < Finset.card (Finset.univ : Finset (Fin (n + 1))) := by
    convert Lagrange.degree_interpolate_lt f _;
    exact hv.injOn;
  rwa [ Finset.card_fin ] at h_deg

/-
`natDegree` version: interpolation produces degree `≤ n`.
-/

/-! ## The evaluation linear map on bounded-degree polynomials -/

/-- Evaluation of a polynomial at the node vector `v`, as a linear map
from `degreeLT K (n+1)` to `Fin (n+1) → K`. -/
noncomputable def evalAtNodes (v : Fin (n + 1) → K) :
    Polynomial.degreeLT K (n + 1) →ₗ[K] (Fin (n + 1) → K) where
  toFun p i := p.1.eval (v i)
  map_add' p q := by ext i; simp [Polynomial.eval_add]
  map_smul' c p := by ext i; simp [Polynomial.eval_smul]

/-! ## The interpolation linear map into bounded-degree polynomials -/

/-- Lagrange interpolation as a linear map into `degreeLT K (n+1)`. -/
noncomputable def interpAtNodes (v : Fin (n + 1) → K)
    (hv : Function.Injective v) :
    (Fin (n + 1) → K) →ₗ[K] Polynomial.degreeLT K (n + 1) where
  toFun f := ⟨(Lagrange.interpolate Finset.univ v) f,
              Polynomial.mem_degreeLT.mpr (degree_interpolate_lt_of_injective v hv f)⟩
  map_add' f g := by
    ext1
    simp [map_add]
  map_smul' c f := by
    ext1
    simp [map_smul]

/-! ## Right inverse: evaluation ∘ interpolation = id -/

/-
Evaluating the Lagrange interpolant at any node recovers the original value.
-/
theorem eval_interp_eq_id (v : Fin (n + 1) → K)
    (hv : Function.Injective v) (f : Fin (n + 1) → K) :
    evalAtNodes v (interpAtNodes v hv f) = f := by
  -- By definition of Lagrange interpolation, we know that for any node \(x_i\), \(\text{eval at node } x_i \circ \text{interp} = \text{id}\).
  have h_eval_interpolate : ∀ i, ((Lagrange.interpolate Finset.univ v) f).eval (v i) = f i := by
    intro i
    apply Lagrange.eval_interpolate_at_node
    · exact hv.injOn
    · exact Finset.mem_univ i
  exact funext h_eval_interpolate

/-! ## Left inverse: interpolation ∘ evaluation = id -/

/-
Interpolating the evaluations of a bounded-degree polynomial at `n+1` distinct
nodes recovers the polynomial, by the uniqueness theorem for polynomial interpolation.
-/
theorem interp_eval_eq_id (v : Fin (n + 1) → K)
    (hv : Function.Injective v) (p : Polynomial.degreeLT K (n + 1)) :
    interpAtNodes v hv (evalAtNodes v p) = p := by
  -- By definition of interpolation, we know that the degree of the interpolating polynomial is less than `n+1`.
  have hdeg : ((Lagrange.interpolate Finset.univ v) fun i ↦ Polynomial.eval (v i) p.val).degree < (n+1 : ℕ) := by
    exact degree_interpolate_lt_of_injective v hv _;
  by_contra h_contra;
  -- By definition of interpolation, we know that the polynomial $p$ and its interpolant agree at the nodes.
  have h_agree : ∀ i : Fin (n + 1), Polynomial.eval (v i) ((Lagrange.interpolate Finset.univ v) (fun i ↦ Polynomial.eval (v i) p.val)) = Polynomial.eval (v i) p.val := by
    intro i; erw [ Lagrange.eval_interpolate_at_node ] ; aesop;
    exact Finset.mem_univ i;
  -- By definition of polynomial degree, if two polynomials of degree less than `n+1` agree at `n+1` distinct points, they must be equal.
  have h_unique : ∀ (f g : Polynomial K), f.degree < (n + 1 : ℕ) → g.degree < (n + 1 : ℕ) → (∀ i : Fin (n + 1), Polynomial.eval (v i) f = Polynomial.eval (v i) g) → f = g := by
    intros f g hf hg hfg;
    refine' Polynomial.eq_of_degree_sub_lt_of_eval_index_eq ( Finset.univ : Finset ( Fin ( n + 1 ) ) ) _ _ _;
    exacts [ v, fun i _ j _ hij => hv hij, lt_of_le_of_lt ( Polynomial.degree_sub_le _ _ ) ( max_lt hf hg ) |> fun h => h.trans_le ( by simp +decide ), fun i _ => hfg i ];
  apply h_contra;
  exact Subtype.ext ( h_unique _ _ hdeg ( by simpa using Polynomial.mem_degreeLT.mp p.2 ) h_agree )

/-! ## The main linear equivalence -/

/-- **Evaluation at `n+1` distinct field points is a `K`-linear equivalence**
from degree-`< (n+1)` polynomials to function values on the nodes, with
Lagrange interpolation as the canonical inverse.

This is the algebraic heart of Reed–Solomon codes, finite sheaf reconstruction,
and polynomial-based symbolic regression. -/
noncomputable def evalOnNodesLinearEquiv (v : Fin (n + 1) → K)
    (hv : Function.Injective v) :
    Polynomial.degreeLT K (n + 1) ≃ₗ[K] (Fin (n + 1) → K) where
  toLinearMap := evalAtNodes v
  invFun := interpAtNodes v hv
  left_inv := interp_eval_eq_id v hv
  right_inv := eval_interp_eq_id v hv


end PolynomialInterpolation


