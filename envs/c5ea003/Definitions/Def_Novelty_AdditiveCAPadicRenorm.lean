-- Prove2me | Definitions.Def_Novelty_AdditiveCAPadicRenorm
-- name    : Novelty_AdditiveCAPadicRenorm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T13:59:57.801328+00:00
-- url     : https://prove2.me/theorems/bf57729a-01b3-4ef2-9b77-15343c2aed3b
-- title:
--   Aether Catalog definitions — Novelty_AdditiveCAPadicRenorm
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AdditiveCAPadicRenorm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AdditiveCAPadicRenorm.lean by skeleton subtraction
import Mathlib

/-!
# Arithmetic Universality in Additive Cellular Automata via p-adic Renormalization

We model a one-dimensional, nearest-neighbour **additive** cellular automaton (CA)
over the finite alphabet `ZMod p` (the field `𝔽_p`, `p` prime) as multiplication
inside the Laurent polynomial ring `(ZMod p)[T; T⁻¹]`.

A bi-infinite configuration `s : ℤ → ZMod p` of finite support is encoded as a
Laurent polynomial `∑ₓ s(x) · Tˣ`.  The local rule of the additive
nearest-neighbour CA (the `𝔽_p` analogue of Wolfram's *Rule 90*) sends a cell to
the sum of its two neighbours, i.e. it acts as multiplication by the operator

  `caOp p = T + T⁻¹`.

Time-`t` evolution is therefore multiplication by `(caOp p) ^ t`, and the entire
space-time diagram is governed by the powers of a single ring element.

The central phenomenon is **p-adic renormalization**: although the binomial
space-time diagram (Pascal's triangle mod `p`) is intricate, at time `p^k` the
operator collapses to a *pure pair of light-cone rays*

  `(caOp p) ^ (p^k) = T^(p^k) + T^(−p^k)`,

a direct consequence of the Frobenius / "freshman's dream" identity in
characteristic `p`.  This is the algebraic heart of the self-similar Sierpiński
structure of these automata and of their arithmetic universality.

## Main results
* `caEvolve_add`, `caEvolve_smul` — the CA evolution operator is `𝔽_p`-linear.
* `caOp_pow_char` — the one-step renormalization `(caOp)^p = T^p + T^(−p)`.
* `caOp_renorm` — the renormalization tower `(caOp)^(p^k) = T^(p^k) + T^(−p^k)`.
* `caOp_renorm_seed` — translation-covariant evolution of a single-cell seed:
  `(caOp)^(p^k) * Tᵃ = T^(a+p^k) + T^(a−p^k)`.
* `caOp_binomial` — the generating-function closed form
  `(caOp)^n = ∑_{k≤n} C(n,k) · T^(2k−n)` (Pascal's triangle mod `p`).

## Catalog synthesis
This file develops a self-contained algebraic theory complementary to the
project's number-theoretic `p`-adic strand (e.g. the lifting-the-exponent and
entry-point machinery in
`Catalog/Algebra/Tropical_p_adic_Valuation_Bounds_and_Lifting_the_Exponent_for_Fibonacci_Primitive_Divisors.lean`,
in particular `add_pow_char`-style Frobenius arguments used there for matrices
over `ZMod p`).  Here the same Frobenius mechanism is repackaged as a
*renormalization-group* statement about cellular automata, bridging the
dynamical-systems and number-theoretic domains of the catalog.
-/

open LaurentPolynomial

noncomputable section

namespace AdditiveCA

variable (p : ℕ) [Fact p.Prime]

/-- The Laurent polynomial ring `(ZMod p)[T; T⁻¹]` is our state space:
a configuration `s : ℤ → ZMod p` of finite support corresponds to `∑ₓ s(x)·Tˣ`. -/
abbrev State (p : ℕ) := LaurentPolynomial (ZMod p)

/-- `(ZMod p)[T; T⁻¹]` inherits characteristic `p` from its field of coefficients,
since the structural map `ZMod p → (ZMod p)[T; T⁻¹]` is injective. -/
instance : CharP (State p) p :=
  charP_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective (ZMod p) (LaurentPolynomial (ZMod p))) p

/-- The additive nearest-neighbour CA operator over `𝔽_p` (the `Rule 90` analogue):
each cell becomes the sum of its two neighbours, i.e. multiplication by `T + T⁻¹`. -/
def caOp (p : ℕ) : State p := T 1 + T (-1)

-- !-- Lab Notebook -- !--
-- Hypothesis: A nearest-neighbour additive CA over 𝔽_p is "linear" in the strong
--   algebraic sense: its time evolution is multiplication by a fixed ring element,
--   hence an 𝔽_p-module endomorphism of the configuration space.
-- Result: `caEvolve_add` / `caEvolve_smul` confirm additivity and 𝔽_p-homogeneity
--   for every power (every time step) of the operator.
-- Insight: Encoding configurations as Laurent polynomials turns "superposition of
--   initial conditions" into the distributive law, so linearity is free.
-- Failure analysis: A naive `ℤ → ZMod p` pointwise model would force manual
--   convolution bookkeeping; the Laurent-polynomial encoding sidesteps it entirely.

-- !-- The CA evolution operator is additive: evolving a superposition of two
-- configurations equals the superposition of the evolutions (left-distributivity). -- !--

-- !-- The CA evolution operator is 𝔽_p-homogeneous: scaling the initial
-- configuration by a constant scales the whole space-time diagram. -- !--

-- !-- Lab Notebook -- !--
-- Hypothesis: At time exactly p the elaborate Pascal-mod-p diagram should collapse,
--   because (a+b)^p = a^p + b^p in characteristic p (Frobenius / freshman's dream).
-- Result: `caOp_pow_char` proves (T + T⁻¹)^p = T^p + T^(−p): a clean pair of rays.
-- Insight: This is the renormalization-group fixed point of the automaton — the
--   p-step map IS the one-step map rescaled spatially by p.  This single identity
--   is the algebraic source of Sierpiński self-similarity.
-- Failure analysis: Needed the `CharP (State p) p` instance; it is not found by
--   default and is supplied above via `charP_of_injective_algebraMap`.

-- !-- One-step p-adic renormalization: by the Frobenius identity in characteristic
-- p, the time-p evolution operator is exactly two light-cone rays T^p + T^(−p). -- !--

-- !-- Renormalization tower: iterating the Frobenius collapse, the time-p^k operator
-- is two rays at distance p^k, exhibiting exact discrete scale invariance. -- !--

-- !-- Translation-covariant seed evolution: a single live cell at position a evolves,
-- after p^k steps, into exactly two live cells at a ± p^k (the renormalized light cone). -- !--

-- !-- Lab Notebook -- !--
-- Hypothesis: The full space-time diagram of the additive CA is governed by binomial
--   coefficients mod p (this is the precise sense in which it computes Pascal's
--   triangle / is "arithmetically universal").
-- Result: `caOp_binomial` gives the exact generating function
--   (T+T⁻¹)^n = ∑_{k≤n} C(n,k)·T^(2k−n).
-- Insight: Combined with `caOp_renorm`, this recovers Lucas-style mod-p structure:
--   the interior binomials vanish at the renormalized scales p^k, leaving only the
--   two extreme terms — exactly the rays of `caOp_renorm`.
-- Failure analysis: The ℕ-subtraction exponent (n−k) needed a guarded cast
--   `((n-k:ℕ):ℤ) = n - k` valid because k ≤ n on the summation range.

-- !-- Generating-function closed form: the time-n diagram is the n-th row of
-- Pascal's triangle mod p, placed on the even/odd sublattice via the binomial theorem. -- !--

/-! ## Computational corollaries (concrete renormalization instances) -/

-- !-- Rule 90 over 𝔽₂: after 4 = 2² steps a single cell becomes two cells at ±4,
-- a concrete instance of the renormalization tower (Sierpiński self-similarity). -- !--

-- !-- Additive CA over 𝔽₃: after 3 steps a single cell becomes two cells at ±3. -- !--

end AdditiveCA


