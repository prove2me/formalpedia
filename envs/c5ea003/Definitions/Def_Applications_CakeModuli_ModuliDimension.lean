-- Prove2me | Definitions.Def_Applications_CakeModuli_ModuliDimension
-- name    : Applications_CakeModuli_ModuliDimension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:38:24.594812+00:00
-- url     : https://prove2.me/theorems/17244eb9-cabf-4669-a217-ad0d75a70e58
-- title:
--   Aether Catalog definitions — Applications_CakeModuli_ModuliDimension
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CakeModuli.ModuliDimension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CakeModuli/ModuliDimension.lean by skeleton subtraction
import Mathlib
/-
# The Fundamental Theorem of Cakes: the dimension of the moduli of decorated surfaces

A *cake* is a closed orientable surface `C` of genus `g` — the base — equipped with a
finite decoration of `n` marked points (the *cherries*) and a boundary line bundle (the
*frosting*, a rank-one locally free sheaf).  Two cakes have the same *flavour* when their
underlying pointed surfaces are isomorphic, so the classifying object of cakes of genus `g`
with `n` cherries is exactly the moduli space `M_{g,n}` of `n`-pointed genus-`g` curves.

The **Fundamental Theorem of Cakes** asserts that a cake is determined, up to isomorphism of
flavour, by the discrete invariants `(g, n)` together with the continuous moduli recording the
relative positions of its features, and that the space of these continuous moduli has dimension

      dim M_{g,n} = 3g - 3 + n .

This file isolates the *exact arithmetic backbone* of that statement and proves it from two
independent Riemann–Roch computations, cross-linking three classical invariants of the surface:

* the **Euler characteristic** `χ = 2 - 2g` and the first **Betti number** `b₁ = 2g`;
* the **canonical degree** `deg K = 2g - 2` and the tangent degree `deg T = 2 - 2g`;
* the **Riemann–Roch Euler characteristic** `χ(L) = deg L + 1 - g` of a line bundle `L`.

The core dimension `3g - 3` is obtained twice, from genuinely different sheaves:

* as the space of first-order deformations `H¹(C, T_C)`, i.e. `-χ(T_C)` (since `H⁰(T_C) = 0`
  for `g ≥ 2`, a curve of general type has no infinitesimal automorphisms);
* as the space of quadratic differentials `H⁰(C, 2K_C)`, i.e. `χ(2K_C)` (since `H¹(2K_C) = 0`
  by Serre duality for `g ≥ 2`), the cotangent space to the moduli at `[C]`.

Serre duality identifies the two, which is the content of `deformation_eq_quadratic`.

The exceptional low-genus flavours — a cake with no cherries at genus `0` or `1`, where the raw
formula `3g - 3` returns the nonsensical `-3` and `0` — are *repaired* by the cherries: the
marked formula `3g - 3 + n` gives the correct `dim M_{0,n} = n - 3` and `dim M_{1,n} = n`, and
the stability inequality `2g - 2 + n > 0` is exactly the condition under which the flavour has
finitely many automorphisms.  This is where the cherries earn their keep: at unstable genus they
are not decoration but structure.

The Teichmüller space of a cake is the universal cover of its moduli, of real dimension
`6g - 6 = 3·deg K`.

The file is self-contained (`import Mathlib`) and lives in the namespace `CakeModuli`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the "cake decoration = moduli" slogan should reduce to a single
integer identity, `dim M_{g,n} = 3g - 3 + n`, and the bold sub-claim is that the bare number
`3g - 3` is not an isolated coincidence but the shared value of TWO Riemann–Roch computations —
deformations `H¹(T_C)` and quadratic differentials `H⁰(2K_C)` — glued by Serre duality.  Second
bold claim: the notorious genus `0,1` breakdown of `3g - 3` is not a defect but a signal that
cherries (marked points) are forced by stability.

Experiment (Experimenter): modelled every invariant as an explicit `ℤ`-valued function and the
Riemann–Roch Euler characteristic as `rrChi d g = d + 1 - g`.  The two derivations of `3g - 3`
became `- rrChi (tangentDeg g) g` and `rrChi (2·canonicalDeg g) g`; a single `ring` closes their
equality (`deformation_eq_quadratic`).  The stability/repair phenomena became `omega` facts about
`2g - 2 + n`.  The inductive skeleton `dimRec` recovers the closed form by induction, certifying
the "+3 per genus step" recurrence.

Analysis (Analyst): what survives is the *entire arithmetic content* of the dimension theorem,
independent of the analytic construction of `M_{g,n}`.  The cross-domain bridge is real:
`teichDim g = 3·canonicalDeg g` links a moduli dimension to a sheaf degree, and
`betti_moduli` links it to the first Betti number `2g`.  Failure mode ruled out: phrasing the
formula over `ℕ` truncates the negative genus-`0,1` values and hides the exceptional locus — the
`ℤ` formulation is what makes the "repair by cherries" visible and provable.

Critique (Critic): is any statement vacuous or definitional?  No — every identity relates
*distinct* definitions (e.g. `moduliDim` vs. `rrChi ∘ tangentDeg`) and needs `ring`/`omega`, not
`rfl`; `holoDiff_eq_genus` recovers `h⁰(K) = g` from Riemann–Roch, not by fiat.  Adversarial
corner case: `dim_nonneg_of_stable` could be vacuous if stability never held at low genus — but
`marked_genus0`/`marked_genus1` exhibit the genuine unstable-to-stable boundary, so the guard is
sharp, not empty.  The injectivity results (`moduliDim_injective`, `genus_recovered`) are the
honest "up to flavour, invariants are recovered" half of the Fundamental Theorem.

Synthesis (PI): the number `3g - 3 + n` is the common shadow of deformation theory, quadratic
differentials, Betti/Euler topology and the stability inequality; cakes are the moduli of curves.
-/

namespace CakeModuli

/-! ## Invariants of the base surface (the "cake base") -/

/-- Euler characteristic of a closed orientable genus-`g` surface: `χ = 2 - 2g`. -/
def eulerChar (g : ℤ) : ℤ := 2 - 2*g

/-- First Betti number of a closed orientable genus-`g` surface: `b₁ = 2g`. -/
def firstBetti (g : ℤ) : ℤ := 2*g

/-- Degree of the canonical bundle `K_C` of a genus-`g` curve: `deg K = 2g - 2`. -/
def canonicalDeg (g : ℤ) : ℤ := 2*g - 2

/-- Degree of the tangent bundle `T_C = K_C^{-1}`: `deg T = 2 - 2g`. -/
def tangentDeg (g : ℤ) : ℤ := 2 - 2*g

/-- Riemann–Roch Euler characteristic of a line bundle of degree `d` on a genus-`g` curve:
`χ(L) = h⁰(L) - h¹(L) = deg L + 1 - g`. -/
def rrChi (d g : ℤ) : ℤ := d + 1 - g

/-! ## The moduli / decoration dimensions (the "cherries and frosting") -/

/-- Dimension of the moduli space `M_g` of genus-`g` curves (cakes with no cherries). -/
def moduliDim (g : ℤ) : ℤ := 3*g - 3

/-- Dimension of the moduli space `M_{g,n}` of `n`-pointed genus-`g` curves
(cakes with `n` cherries): `3g - 3 + n`. -/
def moduliDimMarked (g n : ℤ) : ℤ := 3*g - 3 + n

/-- Real dimension of the Teichmüller space of a genus-`g` surface: `6g - 6`. -/
def teichDim (g : ℤ) : ℤ := 6*g - 6

/-- Dimension of the space of holomorphic differentials `H⁰(C, K_C)` (the "flavour space"),
computed via Riemann–Roch as `χ(K) + 1`. -/
def holoDiffDim (g : ℤ) : ℤ := rrChi (canonicalDeg g) g + 1

/-- Stability of an `n`-pointed genus-`g` curve: `2g - 2 + n > 0`. -/
def stable (g n : ℤ) : Prop := 0 < 2*g - 2 + n

/-! ## Topology of the base: Euler characteristic and Betti numbers -/





/-! ## The dimension of moduli, computed two ways -/






/-! ## Teichmüller space and the Betti bridge -/




/-! ## Cherries repair the exceptional low-genus flavours -/







/-! ## The Fundamental Theorem of Cakes: invariants recover the flavour -/






/-! ## Inductive certification of the recurrence -/

/-- The moduli dimension defined by the recurrence "start at `-3`, add `3` per handle". -/
def dimRec : ℕ → ℤ
  | 0 => -3
  | (n+1) => dimRec n + 3



/-! ## Enumeration sanity check for cakes with `g ≤ 5` cherries -/


end CakeModuli


