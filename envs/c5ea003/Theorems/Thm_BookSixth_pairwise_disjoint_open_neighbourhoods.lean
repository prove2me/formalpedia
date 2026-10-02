-- Prove2me | Theorems.Thm_BookSixth_pairwise_disjoint_open_neighbourhoods
-- name    : BookSixth.pairwise_disjoint_open_neighbourhoods
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T19:59:14.82474+00:00
-- url     : https://prove2.me/theorems/7fd98b02-98b1-425a-82fb-6b515df86aeb
-- title:
--   Pairwise disjoint compact sets have pairwise disjoint open neighbourhoods
-- statement:
--   Let $S_0, \dots, S_{n-1}$ be pairwise disjoint compact subsets of $\mathbb{R}^3$. Then there are pairwise disjoint open sets $U_0, \dots, U_{n-1}$ with $S_i \subseteq U_i$. This is the standard separation consequence of compactness: a compact set and a closed set that are disjoint have disjoint neighbourhoods, and compactness is exactly what makes the finitely many neighbourhoods at once pairwise disjoint rather than merely pairwise for each fixed pair. It is the localisation input for moving a finite family of pairwise disjoint round circles independently: the ambient isotopy that moves one circle must be the identity near all the others, and this is what provides the regions in which that can be arranged.
-- source:
--   Standard general topology, no external source needed. For a compact set $K$ and a closed set $F$ with $K \cap F = \emptyset$, the neighbourhoods are separated by $\mathrm{IsCompact.disjoint\_nhdsSet\_left}$ (Mathlib/Topology/Compactness/Compact.lean:246) applied with the filter of the open complement of $F$, together with $\mathrm{Disjoint.exists\_isOpen\_disjoint\_left}$ in the same file. The finiteness of the index type supplies the finitely many separating neighbourhoods. Needed for BookSixth.perfect_circles_pairwise_unlinked_motion (theorem id f6a7245e-187d-4a69-8b49-100cf7e4a1cc), the only open leaf of BookSixth.sixthEditionExtension, and it consumes the proved child BookSixth.round_circle_is_compact (theorem id 447ecc36-9c38-481b-a4f5-9bc76f5c54a6), which supplies the $\mathrm{IsCompact}$ hypotheses from $\mathrm{RoundCircle}$.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.pairwise_disjoint_open_neighbourhoods {n : ℕ} (S : Fin n → Set Space3) (hS : ∀ i, IsCompact (S i)) (hD : ∀ i j, i ≠ j → Disjoint (S i) (S j)) : ∃ U : Fin n → Set Space3, (∀ i, IsOpen (U i)) ∧ (∀ i, S i ⊆ U i) ∧ (∀ i j, i ≠ j → Disjoint (U i) (U j)) := by sorry
