-- Prove2me | Theorems.Thm_Logic_PhaseRoute_sum_triAlign_mul_fst_thd
-- name    : Logic.PhaseRoute.sum_triAlign_mul_fst_thd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:31:12.022264+00:00
-- url     : https://prove2.me/theorems/95499d39-80f4-4c7d-b62f-2ceaf309b9c2
-- title:
--   Sum triAlign mul fst thd
-- statement:
--   Formal statement of `Logic.PhaseRoute.sum_triAlign_mul_fst_thd` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Logic.PhaseRoute.sum_triAlign_mul_fst_thd(H₃ : G × G → ℝ) :
--       (∑ x : G × G × G, triAlign x * H₃ (x.1, x.2.2)) = ∑ a : G, ∑ c : G, H₃ (a, c) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PhaseRouteTripleAlignment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PhaseRouteTripleAlignment.lean#L150

-- Thm stub generated from Logic/PhaseRouteTripleAlignment.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
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

theorem Logic.PhaseRoute.sum_triAlign_mul_fst_thd(H₃ : G × G → ℝ) :
    (∑ x : G × G × G, triAlign x * H₃ (x.1, x.2.2)) = ∑ a : G, ∑ c : G, H₃ (a, c) := by sorry
