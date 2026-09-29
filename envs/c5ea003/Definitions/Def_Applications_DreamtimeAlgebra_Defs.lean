-- Prove2me | Definitions.Def_Applications_DreamtimeAlgebra_Defs
-- name    : Applications_DreamtimeAlgebra_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:16.879177+00:00
-- url     : https://prove2.me/theorems/566ffec9-228e-4239-be59-29b96a57bc8d
-- title:
--   Aether Catalog definitions — Applications_DreamtimeAlgebra_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.DreamtimeAlgebra.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/DreamtimeAlgebra/Defs.lean by skeleton subtraction
import Mathlib
/-
# Dreamtime Algebra: Aboriginal Kinship Systems as Group Theory

This module formalizes Australian Aboriginal kinship systems (section and subsection
systems) as finite groups with distinguished generators. We introduce the novel
mathematical structure `DreamtimeAlgebra` — a finite abelian group equipped with
"kinship generators" (elements of order 2) representing marriage and descent rules.

## Main definitions

* `DreamtimeAlgebra` — A finite additive abelian group with distinguished order-2
  generators representing marriage and descent
* `KarieraSystem` — The concrete 4-section (Kariera) kinship system on `ZMod 2 × ZMod 2`
* `ArandaSystem` — The concrete 8-subsection (Aranda) system on `ZMod 2 × ZMod 2 × ZMod 2`
* `marriageMap` — The marriage permutation: translation by the marriage generator
* `descentMap` — The descent permutation: translation by the descent generator
* `dreamtimeOp` — The "Dreamtime operator": composition of marriage and descent
* `moietyCount` — The number of distinct moieties (nontrivial marriage rules)
* `kinshipSpectrum` — The set of all valid marriage generators in a DreamtimeAlgebra

## Key results

* The marriage map is a fixed-point-free involution (exogamy)
* Marriage compatibility is a coset condition
* The alternating generations theorem: patrilineal descent cycles with period 2
* The Dreamtime operator is itself an involution
* Classification: kinship generators generate an elementary abelian 2-subgroup
* The kinship spectrum of (ZMod 2)^n has exactly 2^n - 1 elements

## References

* Lévi-Strauss, C. "Les Structures élémentaires de la parenté" (1949)
* Weil, A. "Sur l'étude algébrique de certains types de lois de mariage" (1949)
  — Appendix to Lévi-Strauss, the first algebraic formalization
* Kemeny, J.G., Snell, J.L., Thompson, G.L. "Introduction to Finite Mathematics" (1957)
-/


open Finset ZMod

/-! ## Section 1: The DreamtimeAlgebra Structure -/

/-- A `DreamtimeAlgebra` is a finite additive abelian group equipped with two
distinguished elements of order 2: the **marriage generator** σ and the
**descent generator** δ. These encode the two fundamental kinship operations:
- Translation by σ maps each person's section to their required spouse's section
- Translation by δ maps each person's section to their child's section

The axioms enforce:
1. Both generators are involutions (σ + σ = 0, δ + δ = 0)
2. Both are nontrivial (exogamy: you cannot marry within your own section)
3. They are distinct (marriage ≠ descent)

This structure generalizes the classical Kariera (4-section) and Aranda
(8-subsection) systems of Aboriginal Australia. -/
structure DreamtimeAlgebra where
  /-- The carrier type (set of kinship sections) -/
  G : Type*
  /-- Sections form a finite additive commutative group -/
  [instAddCommGroup : AddCommGroup G]
  [instFintype : Fintype G]
  [instDecEq : DecidableEq G]
  /-- The marriage generator: translation by this element gives the spouse's section -/
  marryGen : G
  /-- The descent generator: translation by this element gives the child's section -/
  descentGen : G
  /-- Marriage generator has order 2: applying marriage twice returns to original section -/
  marry_order2 : marryGen + marryGen = 0
  /-- Descent generator has order 2: grandparent and grandchild share sections -/
  descent_order2 : descentGen + descentGen = 0
  /-- Exogamy axiom: you must marry outside your own section -/
  marry_nontrivial : marryGen ≠ 0
  /-- Descent is nontrivial: children are in a different section from parents -/
  descent_nontrivial : descentGen ≠ 0
  /-- Marriage and descent are distinct kinship operations -/
  marry_ne_descent : marryGen ≠ descentGen

attribute [instance] DreamtimeAlgebra.instAddCommGroup
  DreamtimeAlgebra.instFintype DreamtimeAlgebra.instDecEq

namespace DreamtimeAlgebra

variable (D : DreamtimeAlgebra)





end DreamtimeAlgebra

/-! ## Section 2: The Kariera 4-Section System -/


   -- (1, 1)

/-! ## Section 3: The Aranda 8-Subsection System -/


/-! ## Section 4: Marriage as Coset Membership -/


/-! ## Section 5: Kinship Spectrum -/


/-! ## Section 6: Moiety Structure -/


/-! ## Section 7: Generational Cycles -/


