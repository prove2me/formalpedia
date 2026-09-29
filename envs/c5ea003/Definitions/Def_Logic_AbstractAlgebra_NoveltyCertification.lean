-- Prove2me | Definitions.Def_Logic_AbstractAlgebra_NoveltyCertification
-- name    : Logic_AbstractAlgebra_NoveltyCertification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:24:39.480897+00:00
-- url     : https://prove2.me/theorems/f2d41728-e587-407c-9227-604f43e38f88
-- title:
--   Aether Catalog definitions — Logic_AbstractAlgebra_NoveltyCertification
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.AbstractAlgebra.NoveltyCertification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/AbstractAlgebra/NoveltyCertification.lean by skeleton subtraction
import Mathlib
/-
# Formal Novelty Certification for Theorem Descriptors

A mathematically certified mechanism that assigns to each theorem descriptor
a computable embedding into a normed space and proves that sufficiently large
distance from a certified archive implies non-identity, non-redundancy,
and structural novelty.

## Main Results

- `novelty_of_pointwise_lower_bound`: If all archive elements are at distance ≥ ε
  from d, then d is ε-novel relative to the archive.
- `not_mem_of_positive_novelty`: If the embedding is injective and ε > 0,
  then an ε-novel descriptor is not in the archive.
- `archiveDist_eq_witness`: The archive distance is realized by some witness.
- `novelty_certificate_iff`: Novel ε A d ↔ ∀ a ∈ A, ε ≤ ‖embed d - embed a‖.
- `archiveDist_antitone`: Archive distance is antitone under archive growth.
- `novelty_transfer`: Archive distance is 1-Lipschitz in descriptor space.
- `archiveDist_eq_zero_iff`: Zero archive distance characterizes membership
  (under injectivity).
-/


open Finset

/-! ## Descriptor: a concrete finite record encoding bounded theorem features -/

/-- A `Descriptor` encodes syntactic/semantic features of a theorem statement
as a finite record of natural numbers and booleans. This is a concrete
abstraction over a restricted theorem language. -/
structure Descriptor where
  quantDepth : ℕ
  symbolCount : ℕ
  binderCount : ℕ
  hasEq : Bool
  hasForall : Bool
  hasExists : Bool
  natArity : ℕ
  finArity : ℕ
  boolArity : ℕ
  deriving DecidableEq, Repr

/-! ## Embedding into a normed space -/

/-- Embed a descriptor into `Fin 9 → ℝ` by mapping each field to a coordinate.
The ambient space carries the sup-norm, but our theorems are norm-agnostic. -/
noncomputable def embed (d : Descriptor) : Fin 9 → ℝ :=
  fun i =>
    match i.1, i.2 with
    | 0, _ => (d.quantDepth : ℝ)
    | 1, _ => (d.symbolCount : ℝ)
    | 2, _ => (d.binderCount : ℝ)
    | 3, _ => if d.hasEq then 1 else 0
    | 4, _ => if d.hasForall then 1 else 0
    | 5, _ => if d.hasExists then 1 else 0
    | 6, _ => (d.natArity : ℝ)
    | 7, _ => (d.finArity : ℝ)
    | 8, _ => (d.boolArity : ℝ)
    | n + 9, h => absurd h (by omega)

/-! ## Archive distance and novelty -/

/-- The archive distance of a candidate descriptor `d` from a finite archive `A`
is the minimum distance from `d` to any element of `A` in the embedding space.
Returns 0 for the empty archive. -/
noncomputable def archiveDist (A : Finset Descriptor) (d : Descriptor) : ℝ :=
  if h : A.Nonempty then
    A.inf' h (fun a => ‖embed d - embed a‖)
  else 0

/-- A descriptor `d` is `ε`-novel relative to archive `A` if the archive
distance is at least `ε`. -/
def Novel (ε : ℝ) (A : Finset Descriptor) (d : Descriptor) : Prop :=
  ε ≤ archiveDist A d

/-! ## Core certification theorems -/

/-
**Novelty Certificate (Forward Direction).**
If every archived descriptor lies at distance at least `ε` from `d`,
then `d` is certified `ε`-novel relative to `A`.
-/

/-
**Non-membership from positive novelty.**
If the embedding is injective and `d` has positive novelty,
then `d` is not in the archive.
-/

/-! ## Witness realization -/

/-
**Nearest-Neighbor Witness.**
For any nonempty archive, the archive distance is realized by some
archived descriptor — there exists an actual nearest neighbor.
-/

/-! ## Certificate equivalence -/

/-
**Novelty Certificate Theorem (Equivalence).**
A descriptor is `ε`-novel relative to an archive if and only if
every archived descriptor lies at distance at least `ε`.
-/

/-! ## Extensions -/

/-
**Archive distance is nonneg.**
-/

/-
**Monotonicity under archive growth.**
Adding theorems to the archive can only decrease (or preserve) the
archive distance — more known results means harder to be novel.
-/

/-
**Triangle-transfer novelty (1-Lipschitz).**
Archive distance is 1-Lipschitz in the descriptor embedding:
the novelty of one descriptor bounds the novelty of a nearby descriptor.
-/

/-
**Zero-radius characterization.**
Under injectivity of the embedding, the archive distance is zero
if and only if the descriptor is in the archive.
-/

/-
**Embedding injectivity.**
The 9-dimensional embedding is injective: distinct descriptors map to
distinct points. This is the key property enabling non-membership certificates.
-/


