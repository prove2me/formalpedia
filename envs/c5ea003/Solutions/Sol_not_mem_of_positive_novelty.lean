-- Prove2me | solution 1 for not_mem_of_positive_novelty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:28:15.812714+00:00
-- url     : https://prove2.me/submissions/df745401-bdb7-4b11-ba33-cdab6ed3f02c

-- Sol generated from Logic/AbstractAlgebra/NoveltyCertification.lean
import Mathlib
import Definitions.Def_Logic_AbstractAlgebra_NoveltyCertification
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


/-! ## Embedding into a normed space -/


/-! ## Archive distance and novelty -/



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

theorem solution    (_hinj : Function.Injective embed)
    (A : Finset Descriptor) (d : Descriptor) (ε : ℝ)
    (hA : A.Nonempty)
    (hε : 0 < ε)
    (hnov : Novel ε A d) :
    d ∉ A := by
  -- By contradiction, assume $d \in A$.
  by_contra h_contra;
  -- Since $d \in A$, we have $\|embed d - embed d\| = 0$.
  have h_dist_zero : ‖embed d - embed d‖ = 0 := by
    norm_num;
  -- Since the archive distance is the infimum of the distances, and zero is one of those distances (when a = d), the infimum must be zero.
  have h_inf_zero : archiveDist A d ≤ ‖embed d - embed d‖ := by
    unfold archiveDist;
    split_ifs ; aesop;
  -- Since the archive distance is the infimum of the distances, and zero is one of those distances (when a = d), the infimum must be zero. Therefore, ε ≤ 0, which contradicts hε.
  have h_contra : ε ≤ 0 := by
    exact hnov.trans ( h_inf_zero.trans h_dist_zero.le );
  linarith
