-- Prove2me | Definitions.Def_Shared_MoonshineJExpansion
-- name    : Shared_MoonshineJExpansion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:04:23.646347+00:00
-- url     : https://prove2.me/theorems/54a6a075-b409-42c0-b161-edae7f0e030f
-- title:
--   Aether Catalog definitions — Shared_MoonshineJExpansion
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.MoonshineJExpansion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/MoonshineJExpansion.lean by skeleton subtraction
import Mathlib

/-!
# A machine-verified `q`-expansion of the modular invariant `j`

The Monstrous-Moonshine head-character table records, for each of the `194`
conjugacy classes `g` of the Monster, the coefficient `c_g(1)` of `q` in the
McKay–Thompson series `T_g = q⁻¹ + 0 + c_g(1) q + ⋯`.  The entry for the
identity class `1A` is the coefficient of `q` in `j - 744`, i.e. the famous
`196884 = 196883 + 1` of McKay's observation.

This file *computes that entry from first principles inside Lean*, rather than
importing it as unverified data.  The route is purely formal-power-series
arithmetic over `ℤ`:

* `MoonshineJ.E4` is the Eisenstein series `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`, defined by
  its divisor-sum coefficients;
* `MoonshineJ.deltaPart m = ∏_{k=1}^{m} (1 - q^k)^24` is the truncated
  eta-product, so that `Δ = q · deltaPart ∞`;
* `MoonshineJ.deltaPart_stable` proves that the coefficients of `deltaPart m`
  below degree `N` do **not** depend on `m` once `m ≥ N - 1`, which is what makes
  "the" eta product well defined without any convergence theory;
* `MoonshineJ.E4_cube_agree_delta_mul_j` proves
  `E₄³ ≡ deltaPart 7 · J  (mod q⁸)` with
  `J = 1 + 744 q + 196884 q² + 21493760 q³ + 864299970 q⁴ + ⋯`,
  which is exactly the statement `j = q⁻¹ + 744 + 196884 q + ⋯` since
  `j = E₄³/Δ` and `Δ = q · deltaPart`;
* `MoonshineJ.j_coefficients_unique` shows the tabulated coefficients are
  *forced*: any power series `f` with `E₄³ ≡ deltaPart m · f (mod q⁸)` has the
  same first eight coefficients, because `deltaPart m` is a unit of `ℤ⟦X⟧`;
* `MoonshineJ.j_head_coefficient` is the resulting head-table entry
  `c_{1A}(1) = 196884`, and `MoonshineJ.mckay_head_1A` is McKay's
  `196884 = 196883 + 1`.

As a by-product the same computation verifies the first eight values of the
Ramanujan tau function (`MoonshineJ.tau_values`).

## Method

Formal power series are not computable, so the arithmetic is done on *lists of
integers* (truncated series) with an explicit convolution product, and a small
congruence calculus `MoonshineJ.AgreeBelow N` (`≡ mod Xᴺ`) transfers the
list-level identity — discharged by the kernel with `decide` — to genuine
`PowerSeries ℤ` statements.  `MoonshineJ.agreeBelow_iff_dvd` identifies
`AgreeBelow N` with divisibility by `Xᴺ`, which makes the congruence calculus
(products, powers, cancellation by units) pure ideal theory.
-/

namespace MoonshineJ

open Finset PowerSeries

/-! ## 1. Truncated integer series, represented by lists -/

/-- Coefficient of a truncated series presented as a list (zero beyond the end). -/
def cf (a : List ℤ) (n : ℕ) : ℤ := a.getD n 0


/-- Cauchy convolution of two truncated series. -/
def convol (a b : List ℤ) (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), cf a k * cf b (n - k)

/-- Product of two truncated series, kept to `N` terms. -/
def mulT (N : ℕ) (a b : List ℤ) : List ℤ := (List.range N).map (convol a b)

/-- The constant series `1`, kept to `N` terms. -/
def oneT (N : ℕ) : List ℤ := (List.range N).map (fun k => if k = 0 then 1 else 0)

/-- Powers of a truncated series. -/
def powT (N : ℕ) (a : List ℤ) : ℕ → List ℤ
  | 0 => oneT N
  | m + 1 => mulT N a (powT N a m)

/-- The truncated polynomial `1 - q^n`. -/
def etaAtom (N n : ℕ) : List ℤ :=
  (List.range N).map (fun k => if k = 0 then 1 else if k = n then -1 else 0)

/-- The truncated eta product `∏_{k=1}^{m} (1 - q^k)^24`. -/
def etaProd (N : ℕ) : ℕ → List ℤ
  | 0 => oneT N
  | m + 1 => mulT N (powT N (etaAtom N (m + 1)) 24) (etaProd N m)

/-- The truncated Eisenstein series `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`. -/
def e4T (N : ℕ) : List ℤ :=
  (List.range N).map (fun n => if n = 0 then 1 else 240 * ((∑ d ∈ n.divisors, d ^ 3 : ℕ) : ℤ))

/-- The tabulated head of `q · j`, i.e. the coefficients `c(n-1)` of
`j = q⁻¹ + 744 + 196884 q + ⋯`. -/
def jT : List ℤ :=
  [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600, 4252023300096]

/-- The tabulated Ramanujan tau values `τ(1), …, τ(8)`. -/
def tauT : List ℤ := [1, -24, 252, -1472, 4830, -6048, -16744, 84480]

/-- The power series attached to a list of coefficients. -/
noncomputable def ser (a : List ℤ) : PowerSeries ℤ := PowerSeries.mk (cf a)


/-! ## 2. The congruence calculus `≡ mod Xᴺ` -/

/-- `f` and `g` have the same coefficients in all degrees `< N`. -/
def AgreeBelow (N : ℕ) (f g : PowerSeries ℤ) : Prop := ∀ n < N, coeff n f = coeff n g








/-! ## 3. The list arithmetic computes power-series arithmetic -/






/-! ## 4. The eta product and the Eisenstein series -/

/-- The truncated eta product `∏_{k=1}^{m} (1 - q^k)^24`, as a genuine power
series.  `Δ = q · deltaPart ∞`. -/
noncomputable def deltaPart (m : ℕ) : PowerSeries ℤ := ∏ k ∈ Icc 1 m, (1 - X ^ k) ^ 24



/-- The Eisenstein series `E₄ = 1 + 240 ∑_{n ≥ 1} σ₃(n) qⁿ`. -/
noncomputable def E4 : PowerSeries ℤ :=
  PowerSeries.mk (fun n => if n = 0 then 1 else 240 * ((∑ d ∈ n.divisors, d ^ 3 : ℕ) : ℤ))


/-- The tabulated head of `q · j`. -/
noncomputable def jSeries : PowerSeries ℤ := ser jT

/-! ## 5. Truncation stability: the eta product is well defined -/






/-! ## 6. The verified expansion -/





/-! ## 7. The head-table entry for the identity class -/






/-! ## 8. McKay's observation, on verified numbers

The dimensions of the smallest irreducible representations of the Monster are
`1`, `196883`, `21296876`, `842609326`, `19360062527`, `293553734298`.  The
following identities exhibit the verified `j`-coefficients as non-negative
integral combinations of them — the numerical shadow of the graded Monster
module `V♮`. -/






end MoonshineJ


