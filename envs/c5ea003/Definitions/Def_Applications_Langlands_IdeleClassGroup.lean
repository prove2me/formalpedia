-- Prove2me | Definitions.Def_Applications_Langlands_IdeleClassGroup
-- name    : Applications_Langlands_IdeleClassGroup
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:21.279931+00:00
-- url     : https://prove2.me/theorems/9aa3f4a4-19ac-4420-98bd-3eec8afa07d6
-- title:
--   Aether Catalog definitions — Applications_Langlands_IdeleClassGroup
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Langlands.IdeleClassGroup`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Langlands/IdeleClassGroup.lean by skeleton subtraction
import Mathlib
/-
# The idèle class group, and Hecke characters as its characters (GL(1) automorphic side)

The GL(1) Langlands programme has two sides.  The Galois side and the explicit reciprocity law are
treated in `Catalog.NumberTheory.GL1Correspondence` and
`Catalog.Applications.Langlands.ExplicitReciprocity`.  This file builds the *automorphic* side from
the ground up: the **idèle group** and the **idèle class group** of a number field, on which Hecke
characters live.

Mathlib provides the adèle ring `NumberField.AdeleRing R K` (as a commutative topological ring) and
the diagonal embedding `K → AdeleRing R K`, but it does *not* yet provide the idèle class group.
We construct it:

* `IdeleGroup R K := (AdeleRing R K)ˣ` — the group of idèles (units of the adèle ring).
* `ideleDiag : Kˣ →* IdeleGroup R K` — the diagonal embedding of principal idèles.
* `principalIdeles R K := (ideleDiag R K).range` — the subgroup of principal idèles.
* `IdeleClassGroup R K := IdeleGroup R K ⧸ principalIdeles R K` — the idèle class group.

We then prove the structural facts that make this the right object:

* `ideleDiag_injective` — over a number field, `Kˣ` embeds into the idèles (the diagonal map is
  injective), so the principal idèles really are a copy of `Kˣ`.
* `principalIdelesEquiv : Kˣ ≃* principalIdeles R K` — that copy, as a group isomorphism.
* `ideleClass_mk_surjective` — the class map is surjective (the fundamental exact sequence
  `1 → Kˣ → 𝕀 → C → 1`).
* `heckeCharEquiv` — **Hecke characters are exactly the idèle class characters**: continuous-free
  finite-order Hecke characters, modelled here as `IdeleClassGroup R K →* ℂˣ`, correspond bijectively
  to idèle characters that are trivial on principal idèles.  This is the universal property of the
  quotient and is the precise sense in which "a Hecke character is a character of the idèle class
  group".

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the automorphic side of GL(1) Langlands — the idèle class group `C_K` and
its character group — should be constructible directly on top of Mathlib's adèle ring, even though
Mathlib stops at the adèle ring and the principal *additive* subgroup.  The multiplicative
("idèlic") quotient is the missing object.

Experiment (Experimenter): `(AdeleRing R K)ˣ` is automatically a `CommGroup` (units of a commutative
ring), so the quotient by *any* subgroup is again a `CommGroup` — normality is free.  The diagonal
`Kˣ → 𝕀` is `Units.map` applied to `algebraMap K (AdeleRing R K)`, and its injectivity reduces, via
`Units.ext`, to `AdeleRing.algebraMap_injective` (which needs `NumberField K`).  The
character-correspondence is the universal property `Hom(G/N,A) ≃ {f : Hom(G,A) // N ≤ ker f}`, built
by hand from `QuotientGroup.lift` and `QuotientGroup.mk'`.

Analysis (Analyst): the key structural insight is that *commutativity collapses all the subtlety of
normality*: in the GL(1) (abelian) world the idèle class group is just a quotient `CommGroup`, and
its character group is exactly the principal-trivial idèle characters.  This is why class field
theory is the abelian case — the entire construction is formal once `𝕀` is commutative.  A failed
first attempt deduced injectivity directly on `AdeleRing` elements; the clean route is `Units.ext`
followed by the ring-level injectivity, keeping the proof to four lines.

Critique (Critic): is any result trivial?  `ideleDiag_injective` and `heckeCharEquiv` are genuine —
the former uses `AdeleRing.algebraMap_injective` (a real theorem needing `NumberField K`), the latter
is a hand-built equivalence with `left_inv`/`right_inv` discharged by quotient induction, not
`decide`.  Hidden-assumption check: `NumberField K` is needed *only* for injectivity/`principalIdeles
≅ Kˣ`; the group and quotient constructions hold for any Dedekind base.  No corner case makes the
idèle class group collapse, because `Kˣ ↪ 𝕀` is proper in general.

Synthesis (PI): the idèle class group is now a first-class object in the catalog, with the dictionary
"Hecke character = idèle class character" proved as a universal property — the automorphic foundation
on which the GL(1) correspondence rests.
-/

open NumberField

namespace IdeleClassGroup

noncomputable section

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The **idèle group** of `K`: the units of the adèle ring. -/
abbrev IdeleGroup : Type _ := (AdeleRing R K)ˣ

instance : CommGroup (IdeleGroup R K) := inferInstance

/-- The **diagonal embedding** of `Kˣ` into the idèle group, sending `x` to the principal idèle
`(x, x, x, …)`. -/
abbrev ideleDiag : Kˣ →* IdeleGroup R K :=
  Units.map (algebraMap K (AdeleRing R K)).toMonoidHom

/-- The subgroup of **principal idèles** `(x)ᵥ` for `x ∈ Kˣ`. -/
abbrev principalIdeles : Subgroup (IdeleGroup R K) := (ideleDiag R K).range

/-- The **idèle class group** `C_K = 𝕀_K / Kˣ`: the central object of the automorphic (GL(1))
side of class field theory. -/
abbrev IdeleClassGroupType : Type _ := IdeleGroup R K ⧸ principalIdeles R K

instance : CommGroup (IdeleClassGroupType R K) := inferInstance





end

end IdeleClassGroup


