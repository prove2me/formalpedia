-- Prove2me | Definitions.Def_Applications_LFunctionUniverse_FiniteInvariantCensus
-- name    : Applications_LFunctionUniverse_FiniteInvariantCensus
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:04.16348+00:00
-- url     : https://prove2.me/theorems/f4c46534-94d8-4f80-96ec-f67d3450ebcc
-- title:
--   Aether Catalog definitions — Applications_LFunctionUniverse_FiniteInvariantCensus
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.LFunctionUniverse.FiniteInvariantCensus`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/LFunctionUniverse/FiniteInvariantCensus.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The L-Function Universe: A Cosmic Census of All L-Functions

L-functions (the Riemann zeta function, Dirichlet L-functions, L-functions of
modular forms and Galois representations, ...) are conjecturally organised by the
**Selberg class**: Dirichlet series satisfying analytic continuation, a functional
equation, an Euler product, and the Ramanujan bound.  A guiding structural
philosophy is that a Selberg-class L-function is pinned down by a *finite package
of arithmetic invariants*: its degree, its conductor, its root number, the shifts
appearing in its gamma factor, and a finite list of local Euler data.

This file formalises that philosophy as an explicit **finite-invariant model** of
L-function data, `SelbergDatum`, and proves the headline structural fact suggested
by the census:

> The universe of L-functions, modelled by their finite invariant packages, is
> **countable** — indeed *countably infinite*, so it is in bijection with `ℕ`.

Concretely we build a chain of results:

* `SelbergDatum.toTuple_injective` — the invariant package is faithful data;
* `instCountableSelbergDatum` — hence there are at most countably many L-functions;
* `instInfiniteSelbergDatum` — the Dirichlet family already gives infinitely many;
* `SelbergDatum.exists_equiv_nat` — so the universe is in bijection with `ℕ`;
* the same for the arithmetically **valid** sub-universe `Valid`;
* an explicit **census** of the first 100 conductor levels, with its length,
  conductor list, distinctness, and validity all verified.

### Honest scope

`SelbergDatum` is a *model*: it records exactly the finite invariant package the
census philosophy assigns to an L-function, over countable coefficient rings
(`ℤ`, `ℚ`).  Proving that the analytic Selberg class injects into this model in
the required way is a deep rigidity problem (strong multiplicity one and its
relatives) and is **not** claimed here.  What is proved is that *any* family of
L-functions faithfully described by such finite packages is necessarily countable.
See `FUTURE_DIRECTIONS.md`.
-/

open Function

/-- A **finite invariant package** for an L-function, in the spirit of the Selberg
class census.  All coefficient data lives in countable rings.

* `degree`      — the degree `d` of the functional equation;
* `conductor`   — the conductor `q ≥ 1` (the census-ordering key);
* `rootNumber`  — the root number `ε` (`|ε| = 1`), modelled by a rational pair;
* `gammaShifts` — the finite list of shifts `(λⱼ, μⱼ)` of the gamma factor;
* `eulerData`   — a finite list of local Euler data `(p, coefficients)`.
-/
structure SelbergDatum where
  degree : ℕ
  conductor : ℕ
  rootNumber : ℚ × ℚ
  gammaShifts : List (ℚ × ℚ)
  eulerData : List (ℕ × List ℤ)
deriving DecidableEq

namespace SelbergDatum

/-! ## Step 1: the invariant package is faithful data -/

/-- The invariant package, flattened into a tuple of countable types. -/
def toTuple (d : SelbergDatum) :
    ℕ × ℕ × (ℚ × ℚ) × List (ℚ × ℚ) × List (ℕ × List ℤ) :=
  (d.degree, d.conductor, d.rootNumber, d.gammaShifts, d.eulerData)

/-- Two L-function data are equal as soon as their invariant packages agree: the
package loses no information. -/
theorem toTuple_injective : Injective toTuple := by
  intro a b h
  cases a; cases b
  simp only [toTuple, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  subst h1; subst h2; subst h3; subst h4; subst h5; rfl

/-! ## Step 2: countability of the L-function universe -/

/-- **The L-function universe is countable.**  Because each L-function is pinned
down by a finite package of invariants over countable rings, there are at most
countably many of them. -/
instance instCountableSelbergDatum : Countable SelbergDatum :=
  toTuple_injective.countable


/-! ## Step 3: the universe is infinite (via the conductor tower) -/

/-- The tower of "conductor levels": a degree-`0` placeholder datum of each
conductor `n`.  These witness that there are infinitely many distinct data. -/
def levels (n : ℕ) : SelbergDatum :=
  { degree := 0, conductor := n, rootNumber := (1, 0), gammaShifts := [], eulerData := [] }

/-- Distinct conductors give distinct data. -/
theorem levels_injective : Injective levels := by
  intro a b h
  simpa [levels] using congrArg SelbergDatum.conductor h

/-- **The L-function universe is infinite.** -/
instance instInfiniteSelbergDatum : Infinite SelbergDatum :=
  Infinite.of_injective levels levels_injective

/-! ## Step 4: the universe has exactly the cardinality of `ℕ` -/


/-! ## Step 5: worked members of the universe -/

/-- Arithmetic validity: an honest L-function has positive degree and conductor
`≥ 1`.  (A crude proxy for the Selberg-class axioms usable at the level of the
invariant package.) -/
def IsValid (d : SelbergDatum) : Prop := 1 ≤ d.degree ∧ 1 ≤ d.conductor

/-- The Riemann zeta function: degree `1`, conductor `1`, gamma factor with the
single shift `1/2` (i.e. `Γ_ℝ(s)`). -/
def zeta : SelbergDatum :=
  { degree := 1, conductor := 1, rootNumber := (1, 0),
    gammaShifts := [(1 / 2, 0)], eulerData := [] }


/-- The degree-`1` Dirichlet family, indexed by conductor.  (A stand-in for the
Dirichlet L-functions `L(s, χ)`; each conductor level is present.) -/
def dirichletLike (q : ℕ) : SelbergDatum :=
  { degree := 1, conductor := q, rootNumber := (1, 0), gammaShifts := [], eulerData := [] }

/-- The Dirichlet family is faithful in the conductor. -/
theorem dirichletLike_injective : Injective dirichletLike := by
  intro a b h
  simpa [dirichletLike] using congrArg SelbergDatum.conductor h

theorem dirichletLike_isValid {q : ℕ} (hq : 1 ≤ q) : IsValid (dirichletLike q) :=
  ⟨le_refl 1, hq⟩

/-! ## Step 6: the valid sub-universe is also countably infinite -/

/-- The arithmetically valid sub-universe. -/
def Valid : Type := {d : SelbergDatum // IsValid d}

instance : Countable Valid := by
  unfold Valid; infer_instance

/-- An embedding of `ℕ` into the valid sub-universe via the Dirichlet family. -/
def validEmbed (n : ℕ) : Valid :=
  ⟨dirichletLike (n + 1), dirichletLike_isValid (Nat.succ_le_succ (Nat.zero_le n))⟩

theorem validEmbed_injective : Injective validEmbed := by
  intro a b h
  have : dirichletLike (a + 1) = dirichletLike (b + 1) := congrArg Subtype.val h
  have := dirichletLike_injective this
  omega

instance : Infinite Valid := Infinite.of_injective validEmbed validEmbed_injective


/-! ## Step 7: an explicit census of the first 100 conductor levels -/

/-- The **first 100 elements of the census**, ordered by conductor `1, 2, …, 100`,
using the degree-`1` Dirichlet representative at each conductor level. -/
def census : List SelbergDatum := (List.range' 1 100).map dirichletLike





end SelbergDatum


