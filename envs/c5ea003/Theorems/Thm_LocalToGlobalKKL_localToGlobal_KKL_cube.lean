-- Prove2me | Theorems.Thm_LocalToGlobalKKL_localToGlobal_KKL_cube
-- name    : LocalToGlobalKKL.localToGlobal_KKL_cube
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:53:46.99624+00:00
-- url     : https://prove2.me/theorems/d7ed5891-2caf-4eaa-863e-4962176bfcbf
-- title:
--   Flagship concrete local-to-global KKL theorem (Boolean cube).
-- statement:
--   **Flagship concrete local-to-global KKL theorem (Boolean cube).**
--
--   Fix a coordinate `j` of the `n`-cube (with `n ≥ 2`).  If both links of `j` carry
--   total influence at least `T` — the *local* KKL-type lower bound on each link —
--   then some *global* coordinate `i ≠ j` has influence at least the global average
--   `2T/(n-1)`, stated multiplicatively as `(n-1) * Inf f i ≥ 2T`.
--
--   Thus a lower bound on the influence content of each link is transferred to the
--   existence of a globally influential coordinate.
--
--   ```lean
--   theorem LocalToGlobalKKL.localToGlobal_KKL_cube(f : (Fin n → Bool) → Bool) (j : Fin n)
--       (hn : 2 ≤ n) (T : ℕ)
--       (hfalse : T ≤ LinkTotInf f j false) (htrue : T ≤ LinkTotInf f j true) :
--       ∃ i ∈ univ.erase j, 2 * T ≤ (n - 1) * Inf f i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LocalToGlobalKKL/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LocalToGlobalKKL/Basic.lean#L134

-- Thm stub generated from Cryptography/LocalToGlobalKKL/Basic.lean
import Mathlib
import Definitions.Def_Cryptography_LocalToGlobalKKL_Basic

/-!
# A Local-to-Global KKL Theorem for Influence Functions

This file develops a *local-to-global* principle for coordinate influences, in the
spirit of the Kahn–Kalai–Linial (KKL) theorem and the high-dimensional-expander
"local-to-global" machinery (Kahn–Kalai–Linial 1988; Bafna–Hoory–Kaufman 2022;
Gur–Lifshitz–Liu 2022; Gotlib–Kaufman 2023).

The KKL theorem is a *local* statement about a single Boolean function: any
non-degenerate low-influence function must have a coordinate of large influence.
The **local-to-global** paradigm asks: if the *links* of a simplicial complex each
satisfy a KKL-type property, does the whole complex satisfy a global KKL-type
property?  The engine that makes this work is that **influences self-average over
links**: the global influence of a coordinate is a (weighted) average of its
influences in the links.

We formalise two layers.

## Concrete model: the Boolean cube and its codimension-one links

For `f : (Fin n → Bool) → Bool` we define the (unnormalised) coordinate influence
`Inf f i` as the number of edges of the hypercube in direction `i` on which `f`
changes value.  Fixing a coordinate `j` and a value `b` cuts the cube into a
subcube — the *link* of the vertex `(j, b)` — and `InfSub f j b i` counts the
sensitive `i`-edges inside that subcube.  The key structural fact
(`inf_decomp`) is that

  `Inf f i = InfSub f j false i + InfSub f j true i`,

i.e. every influence splits as the sum of the influences in the two links.
Summing over coordinates gives the local-to-global decomposition
`linktot_decomp`, and combined with pigeonholing we obtain the flagship
concrete statement `localToGlobal_KKL_cube`: if both links of `j` carry total
influence `≥ T`, then some global coordinate has influence `≥ 2T/(n-1)`.

## Abstract engine: local KKL ⟹ global KKL

`abstract_localToGlobal_KKL` isolates the general averaging argument for an
arbitrary weighted family of links: given the self-averaging *bridge*
`I i = ∑ ℓ, w ℓ * Iℓ ℓ i` and the *local KKL hypothesis* that every link has an
influential coordinate (`∃ i, τ ≤ Iℓ ℓ i`), the global total influence is at
least `τ · (∑ ℓ w ℓ)`, and consequently (`abstract_global_influential_coord`)
some global coordinate has influence at least the average `τ·(∑ w)/|ι|`.

Finally `cube_total_via_abstract` shows the concrete Boolean-cube decomposition is
literally an instance of the abstract engine (two links of weight one).
-/

open LocalToGlobalKKL

open Finset

/-! ## Concrete model: the Boolean hypercube -/


variable {n : ℕ}











/-! ### Pigeonhole: some coordinate carries at least the average influence -/

theorem LocalToGlobalKKL.localToGlobal_KKL_cube(f : (Fin n → Bool) → Bool) (j : Fin n)
    (hn : 2 ≤ n) (T : ℕ)
    (hfalse : T ≤ LinkTotInf f j false) (htrue : T ≤ LinkTotInf f j true) :
    ∃ i ∈ univ.erase j, 2 * T ≤ (n - 1) * Inf f i := by sorry
