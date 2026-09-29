-- Prove2me | Definitions.Def_Geometry_QuiverPathAlgebra_StrictUpperNilpotent
-- name    : Geometry_QuiverPathAlgebra_StrictUpperNilpotent
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:55.678983+00:00
-- url     : https://prove2.me/theorems/358edf79-81ed-4342-8db0-70ffe5bcb8ba
-- title:
--   Aether Catalog definitions — Geometry_QuiverPathAlgebra_StrictUpperNilpotent
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.QuiverPathAlgebra.StrictUpperNilpotent`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/QuiverPathAlgebra/StrictUpperNilpotent.lean by skeleton subtraction
import Mathlib

/-!
# Strictly upper triangular matrices are nilpotent of index `n`

The path algebra of a finite acyclic quiver with longest path length `n - 1`
embeds, via a topological order on the `n` vertices, into the algebra of
`n × n` upper triangular matrices, with the *arrow ideal* `𝔽Q≥1` landing inside
the **strictly** upper triangular matrices.  This file proves the algebraic
heart of nilpotency: a product of `n` strictly upper triangular `n × n`
matrices is the zero matrix.

The proof tracks a *shift* invariant: a matrix `M` "has shift `k`" if `M i j = 0`
whenever `j < i + k`.  Strictly upper triangular means shift `1`.  Multiplying a
shift-`k` matrix by a shift-`l` matrix yields shift `k + l`, and shift `n` over
`Fin n` forces the matrix to vanish (since `j < n ≤ i + n` always).

## Main results

* `Matrix.Shift.mul` — shift is additive under matrix multiplication.
* `Matrix.Shift.eq_zero_of_top` — a shift-`n` matrix over `Fin n` is zero.
* `Matrix.listProd_shift` — the product of a list of shift-`1` matrices has shift
  equal to the list length.
* `Matrix.prod_ofFn_strictUpper_eq_zero` — the product of `n` strictly upper
  triangular `n × n` matrices is `0`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): "Bounded path length ⇒ the arrow ideal is nilpotent
of index = number of vertices."  Experiment (Experimenter): the naive
`induction on n` on raw matrix entries stalls; the winning idea was the
quantitative `Shift k` filtration, which makes nilpotency a clean additive law
`Shift k * Shift l = Shift (k+l)` plus the boundary fact `Shift n = 0`.
Analysis (Analyst): this is exactly the associated-graded picture `J^k/J^{k+1}`
of the path algebra, with `k` = path length.  Critique (Critic): we must use
`List.prod` rather than `Finset.prod`, since the matrix monoid is
noncommutative; the order of the product is irrelevant to the conclusion `= 0`.
-/

namespace Matrix

variable {n : ℕ} {R : Type*} [Semiring R]

/-- `Shift k M` means every entry strictly below the `k`-th superdiagonal vanishes:
`M i j = 0` whenever `j < i + k`. -/
def Shift (k : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, (j : ℕ) < (i : ℕ) + k → M i j = 0

/-- A strictly upper triangular matrix has shift `1`. -/
def StrictUpper (M : Matrix (Fin n) (Fin n) R) : Prop := Shift 1 M






end Matrix

/-!
## The symmetrized monomial and standard polynomial are identities of `𝔽Q≥1`

We now harvest the *provable half* of the v19d mission statement: for a finite
acyclic quiver `Q` with longest path length `n - 1`, the degree-`n` symmetrized
monomial `S(x₁,…,xₙ) = ∑_{σ ∈ Sₙ} x_{σ(1)} ⋯ x_{σ(n)}` and the degree-`n`
**standard polynomial** `Sₙ(x₁,…,xₙ) = ∑_{σ} sgn(σ) · x_{σ(1)} ⋯ x_{σ(n)}` both
vanish identically on the principal subalgebra `𝔽Q≥1`, modelled by the strictly
upper triangular `n × n` matrices.

### Relation to the Amitsur–Levitzki theorem
Amitsur–Levitzki (MR36751) states the standard polynomial `S_{2n}` is the
minimal-degree standard identity of the *full* matrix algebra `Mₙ(𝔽)`.  Here is
its nilpotent shadow: on the strictly upper triangular subalgebra the standard
identity already appears in degree `n`, and indeed the *unsigned* symmetrized
monomial vanishes too — which is false for `Mₙ`.  The sign is irrelevant because
every individual monomial is already `0`.
-/

namespace PI

open scoped BigOperators

variable {A : Type*} [Ring A] {n : ℕ}

/-- The degree-`n` symmetrized monomial `∑_{σ} a_{σ(1)} ⋯ a_{σ(n)}`. -/
def symMono (a : Fin n → A) : A :=
  ∑ σ : Equiv.Perm (Fin n), (List.ofFn (fun i => a (σ i))).prod

/-- The degree-`n` standard polynomial `∑_{σ} sgn(σ) · a_{σ(1)} ⋯ a_{σ(n)}`. -/
def stdPoly (a : Fin n → A) : A :=
  ∑ σ : Equiv.Perm (Fin n),
    (Equiv.Perm.sign σ : ℤ) • (List.ofFn (fun i => a (σ i))).prod



variable {R : Type*} [Ring R]



end PI


