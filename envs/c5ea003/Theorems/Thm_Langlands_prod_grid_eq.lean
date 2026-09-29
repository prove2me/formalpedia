-- Prove2me | Theorems.Thm_Langlands_prod_grid_eq
-- name    : Langlands.prod_grid_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:08:41.361734+00:00
-- url     : https://prove2.me/theorems/861f296a-bb0e-4060-a8dd-c17c07af06fa
-- title:
--   The ClebschâGordan index identity.
-- statement:
--   **The ClebschâGordan index identity.**  In any commutative monoid, the product of `F`
--   over the multiset of sums `i + j` with `i â¤ m`, `j â¤ n` (`n â¤ m`) equals the product over
--   `â¨_{r â¤ n} {r, â¦, r + (m + n - 2r)}`.  This is the combinatorial heart of the decomposition
--   `Sym^m â Sym^n = â¨_r Sym^{m+n-2r} â det^r`.
--
--   ```lean
--   theorem Langlands.prod_grid_eq{M : Type*} [CommMonoid M] (F : ℕ → M) :
--       ∀ n m : ℕ, n ≤ m →
--         (∏ i ∈ range (m + 1), ∏ j ∈ range (n + 1), F (i + j))
--           = ∏ r ∈ range (n + 1), ∏ i ∈ range (m + n - 2 * r + 1), F (r + i) := by sorry
--
--
--   variable {R : Type*} [CommRing R]
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/LanglandsGeneralClebschGordan.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/LanglandsGeneralClebschGordan.lean#L30

-- Thm stub generated from Shared/LanglandsGeneralClebschGordan.lean
import Mathlib

/-!
# Langlands functoriality, V: the general Clebsch–Gordan decomposition of `Sym^m × Sym^n`

This file proves the general local Rankin–Selberg / functoriality statement for symmetric
power lifts of an unramified `GL(2)` representation: for all `n ≤ m`,

`L(s, Sym^m π × Sym^n π) = ∏_{r=0}^{n} L(s, Sym^{m+n-2r} π ⊗ χ^r)`,

the L-function avatar of the Clebsch–Gordan decomposition
`Sym^m ⊗ Sym^n = ⨁_{r=0}^{n} Sym^{m+n-2r} ⊗ det^r`.

The proof isolates the entire combinatorial content in `prod_grid_eq`, a statement about an
arbitrary commutative monoid: the multiset of index sums `{i + j : i ≤ m, j ≤ n}` coincides
with `⨄_{r ≤ n} {r, r+1, …, r + (m+n-2r)}`.  The Langlands content is then the observation
that the Satake parameters of `Sym^m π ⊗ Sym^n π` and of `⨁_r Sym^{m+n-2r} π ⊗ χ^r` are both
of the form `a^t b^{m+n-t}` with exactly those index multisets
(`satake_mul_satake` and `satake_twist_gen`).

This generalises `symEuler_tensor_one` (`n = 1`) and `symEuler_tensor_two` (`n = 2`), and its
`m = n = 1` case is the local Gelbart–Jacquet identity `L(π × π) = L(Sym^2 π) L(χ)`.
-/


open Finset PowerSeries

theorem Langlands.prod_grid_eq{M : Type*} [CommMonoid M] (F : ℕ → M) :
    ∀ n m : ℕ, n ≤ m →
      (∏ i ∈ range (m + 1), ∏ j ∈ range (n + 1), F (i + j))
        = ∏ r ∈ range (n + 1), ∏ i ∈ range (m + n - 2 * r + 1), F (r + i) := by sorry
