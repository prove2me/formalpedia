-- Prove2me | Definitions.Def_Bridges_PosetTheory_LorentzianProofComplexity
-- name    : Bridges_PosetTheory_LorentzianProofComplexity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T10:25:40.958652+00:00
-- url     : https://prove2.me/theorems/c31f13d0-70b5-4ddb-a339-838701017781
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_LorentzianProofComplexity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.LorentzianProofComplexity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/LorentzianProofComplexity.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Lorentzian Proof Complexity: Resolution–Certificate Bridge

This file establishes a formal bridge between propositional proof complexity
(resolution refutations of CNF formulas) and Lorentzian certificate complexity
(recursive derivative-tree certificates for polynomial Lorentzianity).

## Main Definitions

* `ResolutionStep` — Inductive type for tree-like resolution derivations
* `resolutionSize` — Size (number of nodes) of a resolution derivation
* `resolutionDepth` — Depth of a resolution derivation tree
* `CertificateTree` — Binary certificate trees modeling derivative branches
* `certificateSize` — Size of a certificate tree
* `certificateDepth` — Depth of a certificate tree
* `resolutionToCertificate` — Translation from resolution derivations to certificate trees
* `certificateToResolution` — Reverse translation from certificate trees to resolution steps

## Main Results

* `simulation_size_bound` — Resolution derivations of size s translate to
  certificate trees of size ≤ 2*s (Theorem 1: Forward Simulation)
* `reverse_simulation_size_bound` — Certificate trees of size s translate to
  resolution derivations of size ≤ s (Theorem 2: Reverse Simulation)
* `resolution_lower_bound_transfers` — Lower bounds on resolution size
  transfer to lower bounds on certificate size (Theorem 3: Transfer)
* `certificate_leaves_le_pow_depth` — Certificate depth bounds the
  number of leaves exponentially (Theorem 4: Structural)

## Keywords

proof complexity, Lorentzian polynomials, Hodge theory, resolution lower bounds,
certificate complexity, Hessian signatures, algebraic proof systems,
combinatorial geometry, computational complexity

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Ben-Sasson–Wigderson, "Short proofs are narrow", JACM, 2001
-/

open Finset BigOperators

noncomputable section

namespace LorentzianProofComplexity

/-! ## Resolution Proof System

We define a tree-like resolution proof system for propositional logic.
A resolution derivation builds clauses from axioms via the resolution rule:
from (C ∨ x) and (D ∨ ¬x), derive (C ∨ D).
-/

/-- A literal is a variable index paired with a polarity (true = positive). -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- A clause is a finite set of literals. -/
abbrev Clause (n : ℕ) := Finset (Literal n)

/-- A tree-like resolution derivation over `n` propositional variables.
    Each node is either an axiom (a clause assumed from the formula)
    or a resolution step combining two sub-derivations by resolving
    on a chosen variable. -/
inductive ResolutionStep (n : ℕ) where
  /-- An axiom: a clause taken directly from the input formula. -/
  | axiom_clause (C : Clause n) : ResolutionStep n
  /-- Resolution: resolve on variable `v` from two sub-derivations.
      From clauses containing (v, true) and (v, false) respectively,
      derive the union minus both literals. -/
  | resolve (v : Fin n) (left right : ResolutionStep n) : ResolutionStep n
  deriving Inhabited


/-- The size of a resolution derivation (number of nodes). -/
def resolutionSize {n : ℕ} : ResolutionStep n → ℕ
  | .axiom_clause _ => 1
  | .resolve _ left right => 1 + resolutionSize left + resolutionSize right

/-- The depth of a resolution derivation tree. -/
def resolutionDepth {n : ℕ} : ResolutionStep n → ℕ
  | .axiom_clause _ => 0
  | .resolve _ left right => 1 + max (resolutionDepth left) (resolutionDepth right)



/-! ## Certificate Trees

Certificate trees model the recursive derivative-tree structure used in
Lorentzian polynomial recognition. Each leaf corresponds to a derivative
evaluation point (multiindex), and each internal node represents a
branching decision in the certificate.
-/

/-- A binary certificate tree over `n` variables.
    Leaves carry multiindices (derivative directions).
    Internal nodes represent branching in the certificate along a variable. -/
inductive CertificateTree (n : ℕ) where
  /-- A leaf: a terminal derivative evaluation at a multiindex. -/
  | leaf (α : Fin n → ℕ) : CertificateTree n
  /-- A branch: split on variable `v`, with left and right sub-certificates. -/
  | branch (v : Fin n) (left right : CertificateTree n) : CertificateTree n
  deriving Inhabited

/-- The size of a certificate tree (number of nodes). -/
def certificateSize {n : ℕ} : CertificateTree n → ℕ
  | .leaf _ => 1
  | .branch _ left right => 1 + certificateSize left + certificateSize right

/-- The depth of a certificate tree. -/
def certificateDepth {n : ℕ} : CertificateTree n → ℕ
  | .leaf _ => 0
  | .branch _ left right => 1 + max (certificateDepth left) (certificateDepth right)




/-! ## Translation: Resolution → Certificate Tree

The forward simulation translates each resolution step into a certificate tree node.
Axiom clauses become leaves (with a multiindex derived from the clause).
Resolution steps become branches (the resolved variable determines the branch).
-/

/-- Convert a clause to a multiindex: count positive occurrences of each variable. -/
def clauseToMultiindex {n : ℕ} (C : Clause n) : Fin n → ℕ :=
  fun i => if (i, true) ∈ C then 1 else 0

/-- Translate a resolution derivation into a certificate tree.
    Resolution on variable v becomes a branch on v.
    Axiom clauses become leaves with the clause's multiindex. -/
def resolutionToCertificate {n : ℕ} : ResolutionStep n → CertificateTree n
  | .axiom_clause C => .leaf (clauseToMultiindex C)
  | .resolve v left right =>
    .branch v (resolutionToCertificate left) (resolutionToCertificate right)

/-! ## Theorem 1: Forward Simulation Size Bound

**Statement**: Every resolution derivation of size `s` translates to a
certificate tree of size exactly `2s - 1` (which is ≤ 2s).

This is the core simulation theorem: it shows that the algebraic certificate
structure can simulate resolution proofs with only linear overhead.
-/

/-
The translation preserves size exactly:
    `certificateSize(translate(R)) = resolutionSize(R)`.
-/

/-
**Theorem 1 (Forward Simulation)**: Resolution derivations of size `s`
    translate to certificate trees of size at most `2 * s`.
    This establishes that Lorentzian certificate trees can simulate
    resolution proofs with linear overhead.
-/

/-
The translation preserves depth exactly.
-/

/-! ## Translation: Certificate Tree → Resolution Step

The reverse simulation translates each certificate tree into a resolution step.
Leaves become axiom clauses, branches become resolution steps.
-/

/-- Convert a multiindex to a clause: each nonzero entry becomes a positive literal. -/
def multiindexToClause {n : ℕ} (α : Fin n → ℕ) : Clause n :=
  Finset.univ.filter (fun i => 0 < α i) |>.image (fun i => (i, true))

/-- Translate a certificate tree into a resolution derivation.
    Branch on variable v becomes resolution on v.
    Leaves become axiom clauses. -/
def certificateToResolution {n : ℕ} : CertificateTree n → ResolutionStep n
  | .leaf α => .axiom_clause (multiindexToClause α)
  | .branch v left right =>
    .resolve v (certificateToResolution left) (certificateToResolution right)

/-! ## Theorem 2: Reverse Simulation Size Bound

**Statement**: Every certificate tree of size `s` translates to a
resolution derivation of size exactly `s` (since the translation is
a direct structural map).
-/

/-
The reverse translation preserves size exactly.
-/

/-
**Theorem 2 (Reverse Simulation)**: Certificate trees of size `s`
    translate to resolution derivations of size at most `s`.
    Combined with Theorem 1, this shows the two proof systems are
    polynomially equivalent in size.
-/

/-
The reverse translation preserves depth exactly.
-/

/-! ## Theorem 3: Lower-Bound Transfer

**Statement**: If every resolution derivation of a formula requires size
at least `L`, then every certificate tree representation requires size
at least `⌈L/2⌉`.

This is the central transfer theorem: proof complexity lower bounds
migrate to certificate complexity lower bounds.
-/

/-
**Theorem 3 (Lower-Bound Transfer)**: Resolution size lower bounds
    transfer to certificate size lower bounds.

    If every resolution refutation has size ≥ L, then every corresponding
    certificate tree has size ≥ (L + 1) / 2.

    The proof works by contrapositive: a small certificate yields a small
    resolution derivation via the reverse simulation, contradicting the
    lower bound.
-/

/-! ## Theorem 4: Structural — Depth Controls Leaf Count

**Statement**: The number of leaves in a certificate tree is at most 2^depth.
This is the key structural theorem connecting certificate geometry to
combinatorial complexity.
-/

/-- The number of leaves in a certificate tree. -/
def certificateLeafCount {n : ℕ} : CertificateTree n → ℕ
  | .leaf _ => 1
  | .branch _ left right => certificateLeafCount left + certificateLeafCount right


/-
**Theorem 4 (Depth–Leaf Bound)**: The number of leaves in a certificate
    tree is at most 2^depth.

    This structural theorem shows that certificate depth controls the
    combinatorial complexity of the certificate, analogous to how
    resolution width controls proof complexity.
-/

/-
Size of a certificate tree is exactly 2 * leafCount - 1.
-/

/-
Depth controls certificate size: size ≤ 2^(depth+1) - 1.
-/

/-! ## Bridge: Forbidden Signatures and Boolean Inconsistency

A "forbidden signature" in the Lorentzian context corresponds to a
multiindex where the Hessian check fails. We formalize how such
failure at a leaf corresponds to a contradiction in Boolean semantics.
-/

/-- A multiindex is "consistent" with a Boolean assignment if whenever
    α(i) > 0, the assignment satisfies the corresponding literal. -/
def multiindexConsistent {n : ℕ} (α : Fin n → ℕ) (τ : Fin n → Bool) : Prop :=
  ∀ i : Fin n, 0 < α i → τ i = true

/-
Two multiindices with contradictory requirements on a variable
    cannot both be consistent with any assignment.
-/

/-! ## Polynomial Bound Machinery

We define the polynomial bound relating resolution and certificate sizes.
-/

/-- Linear polynomial bound: poly(s) = 2s. -/
def linearBound (s : ℕ) : ℕ := 2 * s

/-
The forward simulation satisfies a linear bound.
-/

/-
The reverse simulation satisfies a linear bound.
-/

/-! ## Composition Theorem: Resolution Composed with Translation

The composition of forward and reverse translations gives a derivation
with at most quadratic overhead.
-/

/-
Round-trip composition: translate to certificate and back.
    The composed size is at most 2 * original size.
-/

/-! ## Leaf count equals resolution leaf count under translation -/

/-- The number of leaves in the translated certificate equals the
    number of axiom nodes in the resolution derivation. -/
def resolutionAxiomCount {n : ℕ} : ResolutionStep n → ℕ
  | .axiom_clause _ => 1
  | .resolve _ left right => resolutionAxiomCount left + resolutionAxiomCount right

/-
Translation preserves leaf/axiom count.
-/

end LorentzianProofComplexity


