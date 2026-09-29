-- Prove2me | Definitions.Def_Applications_ChromaticSum_Defs
-- name    : Applications_ChromaticSum_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:21.533304+00:00
-- url     : https://prove2.me/theorems/4dc69282-5bc1-4c77-b3f0-b5da0c47b61d
-- title:
--   Aether Catalog definitions — Applications_ChromaticSum_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ChromaticSum.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ChromaticSum/Defs.lean by skeleton subtraction
import Mathlib
/-
# Chromatic Sum of a finite simple graph — core definitions

This file develops, from scratch, the basic theory of the **chromatic sum**
(a.k.a. *minimum colour sum* / *vertex colouring sum*) `Σ(G)` of a finite simple
graph `G`.

The chromatic sum is the minimum, over all proper colourings `c : V → ℕ` using
positive integer colours, of `∑_v c(v)`.  Unlike the ordinary chromatic number
`χ(G)`, which only cares about the *number* of colours, the chromatic sum is
sensitive to how many vertices receive each colour, and its optimal colourings
can behave counter‑intuitively.

## Motivation

The research mission concerns the conjectured *complexity dichotomy* for the
Chromatic Sum problem on `H`-free graphs (polynomial when `H` is a forest,
NP‑complete when `H` contains a cycle).  Complexity‑theoretic statements are
outside what we formalise here; instead we build the combinatorial substrate:
a rigorous definition of `Σ(G)` and its fundamental structural properties,
on top of which the companion file `Dichotomy.lean` proves and *disproves*
several bold quantitative conjectures about `Σ`.

## Main definitions

* `ChromaticSum.IsProperColoring G c` — `c` is a proper colouring with positive
  colours.
* `ChromaticSum.colorSum c` — `∑_v c v`.
* `ChromaticSum.chromaticSum G` — the chromatic sum `Σ(G)`, defined as an `sInf`.

## Main results

* `ChromaticSum.exists_isProperColoring` — a proper colouring always exists
  (colour all vertices distinctly), so the defining set is non‑empty.
* `ChromaticSum.chromaticSum_mem` — the infimum is attained by an actual
  colouring.
* `ChromaticSum.chromaticSum_le_colorSum` / `ChromaticSum.le_chromaticSum` —
  the universal property of `Σ(G)` as a minimum.
* `ChromaticSum.card_le_chromaticSum` — `|V| ≤ Σ(G)`.
* `ChromaticSum.chromaticSum_bot` — `Σ(⊥) = |V|` (the edgeless graph).
* `ChromaticSum.chromaticSum_mono` — `Σ` is monotone under taking subgraphs
  (more edges ⇒ larger chromatic sum).
-/


open Finset

namespace ChromaticSum

variable {V : Type*} [Fintype V] {G H : SimpleGraph V}

/-- A **proper colouring** of `G` with positive integer colours: every colour is
`≥ 1` and adjacent vertices receive different colours. -/
def IsProperColoring (G : SimpleGraph V) (c : V → ℕ) : Prop :=
  (∀ v, 1 ≤ c v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v

/-- The colour sum `∑_v c v` of a colouring `c`. -/
def colorSum (c : V → ℕ) : ℕ := ∑ v, c v

/-- The set of achievable colour sums of proper colourings of `G`. -/
def ChromaticSumSet (G : SimpleGraph V) : Set ℕ :=
  {s | ∃ c, IsProperColoring G c ∧ colorSum c = s}

/-- The **chromatic sum** `Σ(G)`: the least colour sum of a proper colouring. -/
noncomputable def chromaticSum (G : SimpleGraph V) : ℕ := sInf (ChromaticSumSet G)










end ChromaticSum


