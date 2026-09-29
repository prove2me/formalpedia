-- Prove2me | Definitions.Def_Logic_PhaseRouteTripleAlignment
-- name    : Logic_PhaseRouteTripleAlignment
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:00:35.364982+00:00
-- url     : https://prove2.me/theorems/d4d8e5a5-9862-452a-9be9-0bcc63373155
-- title:
--   Aether Catalog definitions — Logic_PhaseRouteTripleAlignment
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PhaseRouteTripleAlignment`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PhaseRouteTripleAlignment.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
/-
# Degree hierarchy: three-way alignment defeats every pairwise encoding

Two further structural results for the phase-encoding programme.

## 1. Window stability is automatic (`Reindex` section)

Every quantity of the finite-sample calculus (`avg`, `cov`, `varr`, `msse`,
`Rsq`) is invariant under an arbitrary relabelling `e : κ ≃ ι` of the sample
space.  Consequently an *exactly zero* degree-1 effect transfers across windows
with ratio exactly `1`; a measured cross/same ratio different from `1` is
therefore evidence about the estimator, never about a genuine degree-1 signal.

## 2. The degree hierarchy does not stop at `2`

On `G × G × G` (`G` any finite additive commutative group; take `G = ZMod p`)
consider the **three-way alignment** target

  `triAlign (a,b,c) = if a + b + c = 0 then 1 else 0`.

Then `cov_triAlign_pairwise_eq_zero` : *every* predictor built from arbitrary
functions of **pairs** of coordinates,

  `pairwise F G H (a,b,c) = F (a,b) + G (b,c) + H (a,c)`,

has covariance exactly `0` with the target — so the entire degree-`≤2` layer,
interaction encodings included, is blind to it, while the target is trivially
degree-`3` measurable (`Rsq_triAlign_self_eq_one`).

This is the sharp prediction for the next experimental round: if the residual
excess is a `k`-way joint alignment, then encodings of degree `< k` must return
*exactly* zero population gain, no matter how many primes are dialled in.
-/

namespace Logic.PhaseRoute

open Finset

/-! ### Relabelling invariance: window stability of exact statements -/

section Reindex

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]






end Reindex

/-! ### Three-way alignment on a finite abelian group -/

section Triple

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- The three-way alignment target: the indicator of the "zero-sum" hyperplane. -/
noncomputable def triAlign : G × G × G → ℝ :=
  fun x => if x.1 + x.2.1 + x.2.2 = 0 then 1 else 0

/-- A degree-`≤2` predictor: arbitrary functions of each *pair* of coordinates. -/
def pairwise (F : G × G → ℝ) (H₂ : G × G → ℝ) (H₃ : G × G → ℝ) : G × G × G → ℝ :=
  fun x => F (x.1, x.2.1) + H₂ (x.2.1, x.2.2) + H₃ (x.1, x.2.2)









/-! Lifting functions of two coordinates to the triple product. -/















end Triple

end Logic.PhaseRoute


