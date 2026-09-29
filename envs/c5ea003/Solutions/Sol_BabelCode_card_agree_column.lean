-- Prove2me | solution 1 for BabelCode.card_agree_column
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:14:56.495312+00:00
-- url     : https://prove2.me/submissions/374299cf-d110-4893-8ce3-678d49ef053a

-- Sol generated from Shared/BabelCodeasanovelmathematicalstructure/SalvagedBest.lean
import Mathlib
import Definitions.Def_Shared_BabelCodeasanovelmathematicalstructure_SalvagedBest
/-
# Babel codes: Plotkin bound, Lawvere diagonal, and sphere packing

The "Volume" of the Library of Babel with alphabet size `A` and page length `L`
is the Hamming space `Fin L → Fin A`.  A *Babel code* of minimum distance `d` is
a set of volumes pairwise at Hamming distance at least `d`.

This file was recovered from a fragment whose supporting definitions
(`Volume`, `IsBabelCode`, `hammingBall`, and the column-disagreement counting
lemma) were missing.  They are supplied here and every statement is proved
from scratch, with no `sorry` and no appeal to `native_decide`.
-/

open Function

open BabelCode




/-! ## Column counting

The engine of the Plotkin bound: in a single coordinate `j`, the number of
*ordered pairs of codewords agreeing at `j`* is `∑ₐ nₐ²` where `nₐ` counts the
codewords carrying the symbol `a` in position `j`.  Cauchy–Schwarz then bounds
the number of disagreeing pairs. -/






/-! ## Theorem 1: the Plotkin bound

**PEGB**:
- **P**roof: double count the total pairwise Hamming distance of the code; the
  off-diagonal pairs force it to be at least `|C|(|C|-1)d`, while column-by-column
  Cauchy–Schwarz forces it to be at most `L|C|²(A-1)/A`.
- **E**xample: binary codes of length 6 and distance 4 have at most 4 codewords.
- **G**eneralization: the same double count gives the Plotkin bound over any
  alphabet, and equality forces equidistance.
- **B**oundary: the hypothesis `L(A-1) < dA` is essential; without it the bound
  is vacuous (and the natural subtraction would truncate).
-/




/-
**Generalization (stated)**: Plotkin bound with equality characterization.
    Equality holds iff C is an equidistant code (all pairs at exactly distance d).
-/


/-
**Generalization**: Lawvere for arbitrary finite types with |Y| ≥ 2.
-/



/-
**Hamming bound (sphere-packing)**: If balls of radius `t` around codewords
    are disjoint (which holds when min distance ≥ 2t+1), the number of
    codewords times the ball size cannot exceed the library size.
-/



/-!
## FUTURE DIRECTIONS

1. **Harper's vertex isoperimetric inequality**: Among all subsets of {0,1}^n of
   fixed size k, the initial segment in the simplicial order minimizes the vertex
   boundary. *Testable*: verify computationally for n ≤ 6 by exhaustive enumeration.

2. **Spectral gap of the Hamming graph**: The adjacency operator of H(L,A) has
   eigenvalues λ_k = L(A-1) - kA with multiplicity C(L,k)(A-1)^k. The spectral
   gap is A, independent of L. *Testable*: compute the 8×8 adjacency matrix of
   H(3,2) and verify eigenvalues are {3,1,1,1,-1,-1,-1,-3}.

3. **Plotkin bound equality characterization**: Equality in the Plotkin bound holds
   iff the code is equidistant. *Testable*: verify for all binary codes of length 6,
   distance 4 achieving |C| = 4 that all pairwise distances equal 4.

4. **Gilbert-Varshamov lower bound**: There exists a BabelCode with |C| ≥ A^L / V(L,d-1)
   where V is the Hamming ball volume. *Testable*: for A=2, L=7, d=3, verify a code
   of size ≥ 128/29 ≈ 4.4, i.e., size ≥ 5 exists (it does: the [7,4,3] Hamming code
   has 16 codewords).

5. **BabelCode lattice structure**: The set of all BabelCodes ordered by inclusion
   forms a lattice. The meet is intersection (with adjusted distance), the join
   requires recomputing minimum distance. *Testable*: enumerate all BabelCodes
   over {0,1}^3 and verify the lattice axioms.
-/
open BabelCode in
lemma solution{A L : ℕ} (C : Finset (Volume A L)) (j : Fin L) :
    ((C ×ˢ C).filter (fun p => p.1 j = p.2 j)).card
      = ∑ a : Fin A, ((C.filter (fun v => v j = a)).card) ^ 2 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun p : Volume A L × Volume A L => p.1 j) (t := Finset.univ)
      (fun x _ => by simp)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfib : (((C ×ˢ C).filter (fun p => p.1 j = p.2 j)).filter (fun p => p.1 j = a))
      = (C.filter (fun v => v j = a)) ×ˢ (C.filter (fun v => v j = a)) := by
    ext ⟨u, x⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, ⟨h2, h3 ▸ h4⟩⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨⟨h1, h3⟩, h2.trans h4.symm⟩, h2⟩
  rw [hfib, Finset.card_product, sq]
