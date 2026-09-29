-- Prove2me | Definitions.Def_Shared_TropicalBrillNoetherConnector
-- name    : Shared_TropicalBrillNoetherConnector
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:15:16.425538+00:00
-- url     : https://prove2.me/theorems/b3cdb732-8c5f-4537-97c5-e5ab02f3a712
-- title:
--   Aether Catalog definitions — Shared_TropicalBrillNoetherConnector
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.TropicalBrillNoetherConnector`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/TropicalBrillNoetherConnector.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/

/-!
# A specialization connector for tropical Brill--Noether theory

This file isolates the precise logical bridge between classical and tropical
Brill--Noether theory.  A `BNWorld` consists of classical divisors, tropical
divisors, and a tropicalization map satisfying the two conclusions of the
specialization lemma: degree is preserved and rank cannot decrease.

A `LiftData` supplies the converse geometric input: every tropical divisor can
be lifted without changing degree and without decreasing rank.  Under these
two hypotheses, existence of a classical `g^r_d` is equivalent to existence of
a tropical `g^r_d`.  Consequently the classical Brill--Noether criterion
transfers verbatim to the tropical side.

Here `HasSeries d r` means rank *at least* `r`, which is the standard meaning
of the notation `g^r_d` in an existence statement.
-/

namespace TropicalBrillNoetherConnector

/-- The Brill--Noether number `ρ(g,d,r) = g - (r+1)(g-d+r)`. -/
def rho (g d r : ℤ) : ℤ :=
  g - (r + 1) * (g - d + r)


/-- The expected number of independent conditions defining a classical
Brill--Noether locus inside a genus-`g` Picard variety. -/
def expectedConditions (g d r : ℤ) : ℤ :=
  (r + 1) * (g - d + r)




/-- The classical rank associated with a space of global sections of dimension
`h⁰` is `h⁰ - 1`. -/
def sectionRank (h0 : ℕ) : ℤ :=
  (h0 : ℤ) - 1


/-- Abstract data of a classical curve and a tropicalization of it.
The rank inequality is the divisor-specialization inequality. -/
structure BNWorld where
  ClassicalDivisor : Type
  TropicalDivisor : Type
  classicalDegree : ClassicalDivisor → ℤ
  classicalRank : ClassicalDivisor → ℤ
  tropicalDegree : TropicalDivisor → ℤ
  tropicalRank : TropicalDivisor → ℤ
  tropicalize : ClassicalDivisor → TropicalDivisor
  degree_tropicalize : ∀ D, tropicalDegree (tropicalize D) = classicalDegree D
  rank_specialization : ∀ D, classicalRank D ≤ tropicalRank (tropicalize D)

/-- Existence of a classical divisor of degree `d` and rank at least `r`. -/
def ClassicalHasSeries (W : BNWorld) (d r : ℤ) : Prop :=
  ∃ D : W.ClassicalDivisor, W.classicalDegree D = d ∧ r ≤ W.classicalRank D

/-- Existence of a tropical divisor of degree `d` and rank at least `r`. -/
def TropicalHasSeries (W : BNWorld) (d r : ℤ) : Prop :=
  ∃ D : W.TropicalDivisor, W.tropicalDegree D = d ∧ r ≤ W.tropicalRank D


/-- The lifting input needed for the reverse implication.  It deliberately
records only the two invariants relevant to Brill--Noether existence. -/
structure LiftData (W : BNWorld) where
  lift : W.TropicalDivisor → W.ClassicalDivisor
  degree_lift : ∀ D, W.classicalDegree (lift D) = W.tropicalDegree D
  rank_lift : ∀ D, W.tropicalRank D ≤ W.classicalRank (lift D)



/-- The classical Brill--Noether theorem, packaged as a property of a world. -/
def SatisfiesClassicalBrillNoether (W : BNWorld) (g : ℤ) : Prop :=
  ∀ d r : ℤ, ClassicalHasSeries W d r ↔ 0 ≤ rho g d r

/-- The tropical Brill--Noether theorem, packaged as a property of a world. -/
def SatisfiesTropicalBrillNoether (W : BNWorld) (g : ℤ) : Prop :=
  ∀ d r : ℤ, TropicalHasSeries W d r ↔ 0 ≤ rho g d r





end TropicalBrillNoetherConnector


