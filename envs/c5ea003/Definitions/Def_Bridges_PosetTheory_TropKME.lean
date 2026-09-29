-- Prove2me | Definitions.Def_Bridges_PosetTheory_TropKME
-- name    : Bridges_PosetTheory_TropKME
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:48.559306+00:00
-- url     : https://prove2.me/theorems/455d72af-5733-4ca7-99ad-01ad699c1edb
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_TropKME
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.TropKME`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/TropKME.lean by skeleton subtraction
import Mathlib
/-
# Tropical Kernel Mean Embedding

This module formalizes the tropical (max-plus) analogue of kernel mean embeddings
for finite types. The core object sends a weight profile `w : α → EReal` to the
tropical potential

    m_w(y) = ⨆ x, w(x) + k(x, y)

where `k : α → α → ℝ` is a real-valued kernel. The fundamental residuation theory
establishes a Galois connection between tropical embedding and residuation:

    (∀ y, tropKME k w y ≤ m y) ↔ (∀ x, w x ≤ ⨅ y, m y - k x y)

This is the idempotent shadow of classical kernel mean embedding theory.

We work with `EReal` (extended reals ℝ ∪ {-∞, +∞}) to obtain a complete lattice
with well-behaved `iSup`/`iInf`, while restricting the kernel to take real values
so that addition and subtraction remain clean.

## Main results

- `tropKME_mono`: monotonicity of the tropical embedding
- `le_tropKME`: pointwise lower bound `w x + k x y ≤ tropKME k w y`
- `tropKME_residuation_upper`: residuation inequality `w x ≤ ⨅ y, tropKME k w y - k x y`
- `trop_galois`: the Galois connection between embedding and residuation
- `tropKME_reconstruct`: exact reconstruction under separating kernel hypothesis
- `tropKME_injective`: injectivity of the tropical embedding
- `tropKME_eq_iff`: characterization of equality via the embedding
- `tropKME_witness_separation`: witness extraction for distinct weight profiles
- `tropKMEFinset_eq_tropKME_of_univ`: equivalence of Finset and Fintype versions
- `tropDeltaKernel_computation`: explicit formula for the Kronecker kernel

## Mathematical remarks

For real-valued kernels k : α → α → ℝ on finite types with |α| ≥ 2,
the max-plus matrix operation necessarily loses information: the tropical
KME is not injective in general. The `TropSeparatingKernel` structure
captures the reconstruction axiom as a specification; it is satisfiable
when the kernel is allowed to take values in the extended reals (e.g.,
the tropical Dirac kernel with -∞ off-diagonal). The general residuation
and Galois connection theory holds unconditionally.
-/


open scoped BigOperators

/-! ## Core definitions -/

/-- The tropical kernel mean embedding: sends a weight profile to the tropical potential
    `m_w(y) = ⨆ x, w(x) + k(x, y)`. This is the max-plus analogue of classical KME. -/
noncomputable def tropKME {α : Type*} [Fintype α] (k : α → α → ℝ) (w : α → EReal) :
    α → EReal :=
  fun y => ⨆ x, w x + (k x y : EReal)

/-- Finset version of the tropical KME for algorithmic finite-support computation. -/
noncomputable def tropKMEFinset {α : Type*} [DecidableEq α]
    (s : Finset α) (k : α → α → ℝ) (w : α → EReal) :
    α → EReal :=
  fun y => s.sup fun x => w x + (k x y : EReal)

/-- The tropical residuation operator: recovers weights from a tropical potential
    via `x ↦ ⨅ y, m(y) - k(x, y)`. This is the right adjoint of `tropKME k`. -/
noncomputable def tropResiduatedBy {α : Type*} [Fintype α]
    (k : α → α → ℝ) (m : α → EReal) : α → EReal :=
  fun x => ⨅ y, m y - (k x y : EReal)

/-- A tropical separating kernel guarantees exact reconstruction:
    `w(x) = ⨅ y, (tropKME k w)(y) - k(x, y)` for all weight profiles `w`.
    This is the tropical analogue of injectivity + perfect reconstruction. -/
structure TropSeparatingKernel (α : Type*) [Fintype α] where
  k : α → α → ℝ
  reconstruct :
    ∀ w : α → EReal, ∀ x,
      w x = ⨅ y, (tropKME k w y) - (k x y : EReal)

/-- A witness-separating kernel provides the two halves of reconstruction separately:
    an upper bound (always holds by residuation) and a witness for the reverse. -/
structure TropWitnessSeparatingKernel (α : Type*) [Fintype α] where
  k : α → α → ℝ
  upper_residuation :
    ∀ w : α → EReal, ∀ x, w x ≤ ⨅ y, (tropKME k w y) - (k x y : EReal)
  witness :
    ∀ w : α → EReal, ∀ x, ∃ y, (tropKME k w y) - (k x y : EReal) ≤ w x

/-- The tropical Kronecker (delta) kernel: `c` on the diagonal, `d` off-diagonal. -/
def tropDeltaKernel {α : Type*} [DecidableEq α] (c d : ℝ) : α → α → ℝ :=
  fun x y => if x = y then c else d

/-! ## Key arithmetic lemmas -/



/-! ## Pointwise lower bound -/


/-! ## Monotonicity -/

/-
The tropical KME is monotone in the weight profile.
-/

/-! ## Residuation -/

/-
If `tropKME k w ≤ m` pointwise, then `w x ≤ m y - k x y` for all `x, y`.
-/

/-
Residuation upper bound: if `tropKME k w ≤ m`, then `w x ≤ ⨅ y, m y - k x y`.
-/

/-
The fundamental residuation inequality: `w x ≤ ⨅ y, tropKME k w y - k x y`.
    This always holds, without any separating kernel hypothesis.
-/

/-! ## Galois connection -/

/-
The Galois connection between tropical KME and residuation:
    `tropKME k w ≤ m` (pointwise) if and only if `w ≤ tropResiduatedBy k m` (pointwise).
    This is the central structural theorem of the tropical KME theory.
-/

/-! ## Reconstruction and injectivity -/


/-
A witness-separating kernel is a separating kernel:
    the upper bound from residuation plus a matching witness yields equality.
-/
def TropWitnessSeparatingKernel.toSeparating {α : Type*} [Fintype α]
    (K : TropWitnessSeparatingKernel α) : TropSeparatingKernel α where
  k := K.k
  reconstruct w x := by
    refine' le_antisymm _ _;
    · exact K.upper_residuation w x;
    · obtain ⟨ y, hy ⟩ := K.witness w x;
      exact le_trans ( ciInf_le ( Finite.bddBelow_range fun y => tropKME K.k w y - ( K.k x y : EReal ) ) y ) hy

/-
Injectivity of the tropical KME under a separating kernel:
    if two weight profiles produce the same embedding, they are equal.
-/

/-
Characterization of embedding equality: `tropKME K.k w₁ = tropKME K.k w₂ ↔ w₁ = w₂`.
-/

/-
Witness separation: distinct weight profiles produce distinct embeddings.
    This gives a constructive finite witness for nonequality.
-/

/-! ## Finset version -/

/-
The `Finset.univ` version of `tropKMEFinset` equals `tropKME`:
    finite algorithmic computation matches the lattice-theoretic definition.
-/

/-! ## Delta kernel computation -/

/-
The tropical KME with the Kronecker delta kernel has the explicit formula:
    `tropKME (tropDeltaKernel c d) w y = max(w y + c, ⨆ x, w x + d)`.
    The diagonal contribution `w y + c` competes with the off-diagonal sup `⨆ x, w x + d`.
-/

/-
The tropical KME with the delta kernel is bounded by the max of diagonal and
    off-diagonal contributions.
-/

/-! ## Strict witness for distinct profiles -/

/-
If `w₁ x < w₂ x`, then the residual at any `y` satisfies the same strict bound.
-/

/-! ## Closure and idempotency -/

/-
The composition Ψ ∘ Φ (residuate after embedding) is a closure operator:
    it always returns a profile ≥ the original, and applying it twice gives the same result
    as applying it once. This is a consequence of the Galois connection.
-/

/-
Monotonicity of the residuation operator.
-/


