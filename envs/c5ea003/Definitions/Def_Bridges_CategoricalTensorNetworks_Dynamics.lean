-- Prove2me | Definitions.Def_Bridges_CategoricalTensorNetworks_Dynamics
-- name    : Bridges_CategoricalTensorNetworks_Dynamics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:59.879436+00:00
-- url     : https://prove2.me/theorems/f1d53c53-64ef-4208-a62a-75162eeae972
-- title:
--   Aether Catalog definitions — Bridges_CategoricalTensorNetworks_Dynamics
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CategoricalTensorNetworks.Dynamics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CategoricalTensorNetworks/Dynamics.lean by skeleton subtraction
import Mathlib

/-!
# Categorical tensor-network dynamics

This file develops a **research direction at the interface of category theory and the
dynamics of tensor networks**, carried out entirely through formal proofs rather than
informal analogy.  The guiding thesis is:

> *A tensor network is a morphism in a monoidal category; its contraction is a monoidal
> functor; and its dynamics is the orbit of a transfer endomorphism under composition.*

We make each clause of this slogan into theorems.

## The dictionary

| Tensor-network notion            | Categorical notion                              |
| -------------------------------- | ----------------------------------------------- |
| a tensor with in/out legs        | a morphism `m ⟶ n` in `Mat K`                   |
| sequential contraction of legs   | composition `≫` (matrix product)                |
| side-by-side (parallel) tensors  | monoidal product `⊗` (Kronecker product)        |
| contraction-order independence   | associativity + the interchange law             |
| 1-D network, periodic boundary   | the categorical trace, `tr (Tᵏ)`               |
| time / spatial evolution         | iterated composition `T ↦ Tᵏ` (the orbit)       |
| bond-index gauge freedom         | conjugation by a unit (similarity invariance)   |
| independent subsystems           | a strong monoidal functor to the ground field   |

## Main results

* `§1` — `Mat K` is a category: `tensor_comp_assoc`, `id_tensor_comp`, `tensor_comp_id`.
* `§2` — Kronecker product is a monoidal **bifunctor**: `tensor_interchange`,
  `tensor_unit`, exhibiting contraction order independence (`tensor_comp_interchange`).
* `§3` — the 1-D periodic partition function is the trace of a transfer-matrix power
  (`partitionFunction`), with `partitionFunction_zero`, the dynamical semigroup law
  `transfer_pow_add`, and cyclic (translation) invariance `partitionFunction_cyclic`.
* `§4` — **gauge invariance**: conjugating the bond index by any invertible gauge leaves
  every partition function unchanged (`partitionFunction_gauge_invariant`).
* `§5` — **spectral / thermodynamic** content: for a diagonalised transfer matrix the
  partition function is the power sum of eigenvalues (`partitionFunction_diagonal`), and
  it is bounded below by the dominant eigenvalue (`partitionFunction_dominant_le`).
* `§6` — the **decoupling** theorem: contraction is strong monoidal, so the partition
  function of a Kronecker (parallel) network factorises (`partitionFunction_kronecker`).
* `§7` — the **abstract categorical backbone**: in any monoidal category the interchange
  law governs parallel-vs-sequential contraction (`monoidal_interchange`,
  `monoidal_parallel_serial`).
-/

namespace Bridges.CategoricalTensorNetworks

open Matrix Finset
open scoped Kronecker

universe u

variable {K : Type*} [Field K]

/-! ## §1. Tensors as morphisms in the category `Mat K`

A tensor with input legs indexed by `n` and output legs indexed by `m` is a matrix
`Matrix m n K`.  Contracting a shared index is matrix multiplication; the bare wire is
the identity matrix.  We record the three category axioms. -/

/-- A tensor: a morphism `n ⟶ m` in the category `Mat K` of matrices over `K`. -/
abbrev Tensor (K : Type*) (m n : Type*) := Matrix m n K

/-
**Associativity of contraction** (category axiom): contracting `(A∘B)∘C` and
`A∘(B∘C)` give the same network, so contraction order does not matter.
-/

/-
**Left identity** (category axiom): pre-composing with a bare wire changes nothing.
-/

/-
**Right identity** (category axiom): post-composing with a bare wire changes nothing.
-/

/-! ## §2. The monoidal product: Kronecker bifunctoriality

Placing two tensors side by side is the Kronecker (tensor) product `A ⊗ₖ B`.  The
content of "`Mat K` is a *monoidal* category" is that `⊗ₖ` is a bifunctor: it preserves
identities and respects composition.  The latter is the **interchange law**, the precise
statement that a planar tensor network may be contracted column-by-column or
row-by-row with the same result. -/

/-
**Interchange law / bifunctoriality of `⊗ₖ`.**  Contracting two parallel wires and
then juxtaposing equals juxtaposing and then contracting.  This is the categorical
heart of contraction-order independence for 2-D networks.
-/

/-
The monoidal product preserves identities: a pair of bare wires is a bare wire.
-/

/-
**Contraction-order independence** for a `2 × 2` block of a network: the two ways of
contracting a square of tensors (parallel-then-serial vs. serial-then-parallel) agree.
-/

/-! ## §3. Transfer-matrix dynamics

For a translation-invariant 1-D network with periodic boundary conditions, the full
contraction (partition function) of `k` copies of a square local transfer tensor `T` is
the categorical **trace** of `Tᵏ`.  "Dynamics" is the orbit `k ↦ Tᵏ` under composition,
a one-parameter discrete semigroup. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The partition function of the periodic 1-D network built from `k` copies of the
square transfer tensor `T`: the trace of the `k`-th composition power. -/
def partitionFunction (T : Matrix n n K) (k : ℕ) : K := (T ^ k).trace

/-
The empty (length-0) network evaluates to the dimension of the bond space: the trace
of the identity, i.e. the number of bond states.
-/

/-
**Dynamical semigroup law.**  Composing a length-`a` and a length-`b` segment yields
the length-`(a+b)` transfer operator; iterating the transfer endomorphism is additive in
the exponent.
-/

/-
**Translation (cyclic) invariance.**  Cutting the periodic chain between segments `a`
and `b` and reconnecting the other way leaves the partition function unchanged: this is
the cyclic invariance of the trace, i.e. the rotational symmetry of the network on the
circle.
-/

/-! ## §4. Gauge invariance of the bond index

A tensor network has a *gauge freedom*: inserting `G⁻¹ G = 1` on any internal bond
(conjugating the transfer matrix by an invertible `G`) is physically invisible.  This is
similarity invariance of the trace of powers. -/

/-
**Gauge invariance.**  Conjugating the transfer matrix by any invertible gauge `G`
leaves every partition function unchanged.
-/

/-! ## §5. Spectral and thermodynamic content

If the transfer matrix is diagonalised (its bonds are eigenmodes), the partition
function is the **power sum of eigenvalues** `∑ᵢ λᵢᵏ`.  In the thermodynamic limit the
sum is governed by the dominant eigenvalue; we record the corresponding lower bound over
the reals. -/

/-
For a diagonal transfer matrix, the partition function is the power sum of the
diagonal eigenvalues `∑ᵢ (dᵢ)ᵏ`.
-/

/-
**Dominant-eigenvalue bound.**  With non-negative real eigenvalues, the partition
function is at least the `k`-th power of any single eigenvalue: the free energy is
controlled from below by the largest eigenvalue.
-/

/-! ## §6. Decoupling: contraction is a strong monoidal functor

Evaluating (fully contracting) a network is a **strong monoidal functor** to the ground
field `K`.  Hence the partition function of a Kronecker (parallel/independent) network
*factorises* as the product of the partition functions of the factors — the categorical
form of statistical independence of decoupled subsystems. -/

/-
The composition power of a Kronecker product splits factorwise:
`(A ⊗ₖ B)ᵏ = Aᵏ ⊗ₖ Bᵏ`.  This is functoriality of `(·)ᵏ` through the monoidal product.
-/

/-
**Decoupling theorem.**  The partition function of a parallel (Kronecker) network is
the product of the partition functions of its independent factors.
-/

/-! ## §7. The abstract categorical backbone

Everything above is an instance of a single law in an arbitrary monoidal category: the
**interchange law**.  We state it abstractly to make explicit that contraction-order
independence is not special to matrices but is the defining coherence of a monoidal
category. -/

open CategoryTheory MonoidalCategory

/-
**Abstract interchange law.**  In any monoidal category, juxtaposing two composites
equals composing two juxtapositions.
-/

/-
**Parallel-vs-serial contraction**, abstractly: the two evaluation orders of a square
of morphisms coincide in every monoidal category.
-/

end Bridges.CategoricalTensorNetworks


