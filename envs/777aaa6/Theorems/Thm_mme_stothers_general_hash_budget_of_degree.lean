-- Prove2me | Theorems.Thm_mme_stothers_general_hash_budget_of_degree
-- name    : mme_stothers_general_hash_budget_of_degree
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T17:18:13.330811+00:00
-- url     : https://prove2.me/theorems/b77dc33d-77ba-4cdd-8c14-14bb3fa22901
-- title:
--   A good hash state from a star-degree bound
-- statement:
--   **One good hash state exists, at any profile.**
--
--   Fix an integral ten-class profile $\beta$, a scale $m\ge1$, an odd prime $p\ge9$, and a
--   progression-free $S$ below $p/2$. Suppose the exact-profile targets number $V D_*$, that every
--   completion star in the ambient family has at most $D$ members, and that the margin condition
--
--   $$p^{2}\,\ell + 3D_*D \;\le\; D_*\,|S|$$
--
--   holds for a loss factor $\ell$. Then some affine hash state retains a vertex-closed family $E$ with
--
--   $$\#\{\text{target--ambient collisions in } E\} + V\ell \;\le\; \#\{\text{targets in } E\}.$$
--
--   This is the probabilistic heart of Davie--Stothers Lemma 3.3, in its deterministic averaging form.
--   The two incidence identities say that summed over all $p^{N+2}$ states the targets contribute
--   exactly $|T||S|p^{N}$ and the collisions at most $|C|p^{N}$, with $|C|\le 3|T|D$ from the star-degree
--   hypothesis. The margin condition is exactly what makes the average of
--   $(\text{targets}) - (\text{collisions})$ at least $V\ell$, so some state beats the average; and every
--   retained family is vertex-closed, because on a supported mixed edge the three hashes form a
--   three-term progression in $S$.
--
--   The retained family is then handed to the deterministic pruning step, which turns it into an induced
--   mode-disjoint family of exact-profile addresses.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_affine_hash
import Mathlib.Combinatorics.Additive.AP.Three.Defs

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_hash_budget_of_degree
    (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r) (m p D Dstar : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp9 : 9 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (V loss : ℝ) (hV : 0 ≤ V)
    (hT : ((MME.StothersFourth.genHashAllTargetEdges base m).card : ℝ) =
      V * (Dstar : ℝ))
    (hdeg : ∀ i : Fin 3, ∀ a ∈ MME.StothersFourth.genHashAllTargetEdges base m,
      ((MME.StothersFourth.genHashMarginalUniverse base m).filter
        (fun b ↦ b.1 i = a.1 i)).card ≤ D)
    (hmargin :
      (p : ℝ) ^ 2 * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ)) :
    ∃ E : Finset (MME.StothersFourth.GenMarginalSupportedAddress base m),
      MME.StothersFourth.GenMarginalVertexClosed E ∧
        ((MME.StothersFourth.genTargetAmbientCollisions E).card : ℝ) + V * loss ≤
          ((MME.StothersFourth.genExactTargetEdges E).card : ℝ) := by
  sorry
