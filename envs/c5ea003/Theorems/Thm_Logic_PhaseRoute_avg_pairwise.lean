-- Prove2me | Theorems.Thm_Logic_PhaseRoute_avg_pairwise
-- name    : Logic.PhaseRoute.avg_pairwise
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:31:01.76307+00:00
-- url     : https://prove2.me/theorems/70988a6a-218a-4016-87b0-f344c89bddcb
-- title:
--   Avg pairwise
-- statement:
--   Formal statement of `Logic.PhaseRoute.avg_pairwise` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Logic.PhaseRoute.avg_pairwise(F H₂ H₃ : G × G → ℝ) :
--       avg (pairwise F H₂ H₃)
--         = ((∑ a : G, ∑ b : G, F (a, b)) + (∑ b : G, ∑ c : G, H₂ (b, c))
--             + ∑ a : G, ∑ c : G, H₃ (a, c)) / ((Fintype.card G : ℝ) ^ 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PhaseRouteTripleAlignment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PhaseRouteTripleAlignment.lean#L214

-- Thm stub generated from Logic/PhaseRouteTripleAlignment.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteLeastSquares
import Definitions.Def_Logic_PhaseRouteTripleAlignment
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

open Logic.PhaseRoute

open Finset

/-! ### Relabelling invariance: window stability of exact statements -/


variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]







/-! ### Three-way alignment on a finite abelian group -/


variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]











/-! Lifting functions of two coordinates to the triple product. -/




omit [DecidableEq G] in

theorem Logic.PhaseRoute.avg_pairwise(F H₂ H₃ : G × G → ℝ) :
    avg (pairwise F H₂ H₃)
      = ((∑ a : G, ∑ b : G, F (a, b)) + (∑ b : G, ∑ c : G, H₂ (b, c))
          + ∑ a : G, ∑ c : G, H₃ (a, c)) / ((Fintype.card G : ℝ) ^ 2) := by sorry
