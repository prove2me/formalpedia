-- Prove2me | Definitions.Def_Novelty_YoungConjugation
-- name    : Novelty_YoungConjugation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:54:27.122728+00:00
-- url     : https://prove2.me/theorems/f08bf56c-6ff2-4f12-b85a-32e59a38eb32
-- title:
--   Aether Catalog definitions — Novelty_YoungConjugation
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.YoungConjugation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/YoungConjugation.lean by skeleton subtraction
import Mathlib
/-
# Young Conjugation as a Z/2Z Symmetry (the algebraic side of the triangle-map involution)

This file isolates the *combinatorial* engine behind the "Young conjugation induces a
measure-preserving involution" story: **Young conjugation of integer partitions**, realised
in Mathlib as `YoungDiagram.transpose`.

We prove that Young conjugation is a genuine order-two element of the permutation group
`Equiv.Perm YoungDiagram` (i.e. a faithful `ℤ/2ℤ` action on the set of all partitions), and
that it preserves the size `|λ| = |λ'|` of a partition.  On the geometric side (see
`NaturalExtensionInvolution.lean` and `ConjugationBridge.lean`) the very same coordinate swap
becomes a measure-preserving involution of the natural-extension domain of the triangle map.

-- !-- Lab Notes -- !--
Hypothesis (H1): Young conjugation `λ ↦ λ'` is an involution of *finite order two*, not merely
  an involutive function; concretely `orderOf` its induced permutation is exactly `2`.
Experiment: `YoungDiagram.transpose_transpose` gives involutivity for free.  The `orderOf = 2`
  claim additionally requires a *witness* of non-triviality: some diagram with `λ' ≠ λ`.  We
  computed the row `[2]` (two cells in one row); its transpose is the column `[1,1]`, and the
  cell `(1,0)` distinguishes them (`decide`).
Analysis: The `orderOf = 2` statement is strictly stronger than involutivity — it certifies
  that conjugation is a non-trivial element of the symmetric group on partitions, hence a
  faithful embedding `ℤ/2ℤ ↪ Equiv.Perm YoungDiagram`.  The size-preservation `card_transpose`
  is what later forces the four geometric subdomains to have *equal* measure.
Critique: `orderOf_eq_prime` needs both `x ^ 2 = 1` and `x ≠ 1`; a vacuous proof would drop the
  second, so we supply the explicit `rowTwo` witness (self-conjugacy failure) — no hidden
  triviality.
Synthesis: Young conjugation = a concrete `ℤ/2ℤ` living inside `Equiv.Perm YoungDiagram`,
  size-preserving.  This is the algebraic template the geometric involution refines.
-/

open YoungDiagram

namespace TriangleMap

/-- **Young conjugation** on partitions, packaged as a permutation of the type of all
Young diagrams.  It is `YoungDiagram.transpose` viewed as an involutive `Equiv`. -/
noncomputable def youngConj : Equiv.Perm YoungDiagram :=
  Function.Involutive.toPerm YoungDiagram.transpose YoungDiagram.transpose_transpose



/-- The row `[2]` (two boxes in a single row); its conjugate is the column `[1,1]`.  This is our
non-self-conjugate witness. -/
noncomputable def rowTwo : YoungDiagram := YoungDiagram.ofRowLens [2] (by decide)





end TriangleMap


