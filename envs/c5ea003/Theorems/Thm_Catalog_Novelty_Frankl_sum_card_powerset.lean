-- Prove2me | Theorems.Thm_Catalog_Novelty_Frankl_sum_card_powerset
-- name    : Catalog.Novelty.Frankl.sum_card_powerset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:09:29.225806+00:00
-- url     : https://prove2.me/theorems/d6db6ec5-c979-47b7-ae7d-1d0bf1fe88cd
-- title:
--   Sum card powerset
-- statement:
--   Formal statement of `Catalog.Novelty.Frankl.sum_card_powerset` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Novelty.Frankl.sum_card_powerset(n : ℕ) :
--       ((Finset.univ : Finset (Fin n)).powerset.sum (fun A => A.card)) = n * 2 ^ (n - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FranklLattice.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FranklLattice.lean#L56

-- Thm stub generated from Novelty/FranklLattice.lean
import Mathlib
import Definitions.Def_Novelty_FranklUnionClosed

/-!
# Lattice reformulation and the tight case of Reimer's entropy bound

Two strands of the union-closed circle of ideas:

## Lattice reformulation
A union-closed family ordered by `⊆` is a finite join-semilattice whose join is
`∪`.  We make this precise with `sup_id_isGreatest`: a nonempty union-closed
family has a greatest element, namely the union `F.sup id` of all its members,
which moreover lies in `F`.

## Reimer's entropy bound — the extremal Boolean cube
Reimer's theorem states that the average member size of a union-closed family `F`
is at least `½·log₂|F|`.  Equality is attained by the **full Boolean lattice**
`𝒫(Fin n)`.  We verify this extremal identity exactly, with no logarithms, by
proving the two integer identities

* `sum_card_powerset` : `Σ_{A ⊆ Fin n} |A| = n · 2^(n-1)`, and
* `card_powerset_univ` : `|𝒫(Fin n)| = 2^n`,

and combining them into `reimer_tight_cube`:
`2 · Σ_{A ⊆ Fin n} |A| = n · |𝒫(Fin n)|`, i.e. the average size is exactly
`n/2 = ½·log₂(2^n)`.  This pins down the equality case of Reimer's inequality.

-- !-- Lab Notes -- !--
Hypothesis (H4): Reimer's `½·log₂|F|` average-size bound is *tight* and the cube
is an extremiser.  Surprising angle (H5): the tightness can be stated and proved
entirely over `ℕ` with no entropy/logarithm machinery, as `2·Σ|A| = n·2^n`.
Experiment: proved `Σ_{A⊆Fin n}|A| = n·2^(n-1)` by double counting (each point
lies in exactly half of all subsets).
Analysis: the double-counting identity is the combinatorial heart of Reimer's
equality case; it is what an entropy proof reproduces asymptotically.
Critique: we deliberately do NOT claim Reimer's inequality in general (that needs
Shearer/entropy); we claim and prove only the extremal identity, which is a
genuine, checkable theorem rather than a restatement.
-/

open Catalog.Novelty.Frankl

open Finset

variable {α : Type*} [DecidableEq α]


/-
Double counting: the total size over all subsets of `Fin n` is `n · 2^(n-1)`.
-/

theorem Catalog.Novelty.Frankl.sum_card_powerset(n : ℕ) :
    ((Finset.univ : Finset (Fin n)).powerset.sum (fun A => A.card)) = n * 2 ^ (n - 1) := by sorry
