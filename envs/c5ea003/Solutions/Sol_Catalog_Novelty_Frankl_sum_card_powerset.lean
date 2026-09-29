-- Prove2me | solution 1 for Catalog.Novelty.Frankl.sum_card_powerset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:58:57.912024+00:00
-- url     : https://prove2.me/submissions/2d76dcbe-6e21-42ad-97b7-8b1f835bf204

-- Sol generated from Novelty/FranklLattice.lean
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

/-
The number of subsets of `Fin n` is `2^n`.
-/



open Catalog.Novelty.Frankl in
theorem solution(n : ℕ) :
    ((Finset.univ : Finset (Fin n)).powerset.sum (fun A => A.card)) = n * 2 ^ (n - 1) := by
  rw [ Finset.sum_eq_multiset_sum ];
  erw [ Multiset.map_coe ];
  have h_sum : ∀ (n : ℕ), ∑ A ∈ Finset.powerset (Finset.univ : Finset (Fin n)), A.card = n * 2 ^ (n - 1) := by
    intro n
    have h_sum : ∑ A ∈ Finset.powerset (Finset.univ : Finset (Fin n)), A.card = ∑ k ∈ Finset.range (n + 1), k * Nat.choose n k := by
      rw [ Finset.sum_powerset ];
      simp +decide;
      exact Finset.sum_congr rfl fun x hx => by rw [ Finset.sum_congr rfl fun y hy => Finset.mem_powersetCard.mp hy |>.2 ] ; simp +decide [ mul_comm ] ;
    rw [ h_sum, ← Nat.sum_range_choose, Finset.mul_sum ];
    cases n <;> simp +arith +decide [ Finset.sum_range_succ', mul_comm, Nat.add_one_mul_choose_eq ];
  convert h_sum n using 1
