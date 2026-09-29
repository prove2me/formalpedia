-- Prove2me | Theorems.Thm_mme_stothers_general_hash_retained_vertex_closed
-- name    : mme_stothers_general_hash_retained_vertex_closed
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T17:04:55.7751+00:00
-- url     : https://prove2.me/theorems/4cd281e3-9cf6-44fb-bc56-ae0a074c02ee
-- title:
--   Vertex closure of the retained hash family
-- statement:
--   **The family retained at one affine hash state is vertex-closed.**
--
--   Fix an integral ten-class profile $\beta$, a scale $m$, an odd modulus $p$, a weight vector $w$ and
--   an affine offset $b_0$, and a progression-free set $S\subseteq\{0,\dots,\lfloor p/2\rfloor-1\}$.
--   Retain those marginal-supported addresses whose three mode hashes $X,Y,Z$ all take a common value
--   in $S$. Then the retained family is *vertex-closed*: whenever three retained addresses $x,y,z$ have
--   a coordinatewise-supported mixed address $(x_1,y_2,z_3)$, that mixed address is itself retained.
--
--   The mechanism is the one Davie--Stothers use in Lemma 3.3. On any supported mixed edge the three
--   $d=8$ hashes satisfy $X + Y = 2Z$ identically, because the grades at each position sum to $8$; so
--   the three retained values $s_x, s_y, s_z \in S$ form a three-term arithmetic progression modulo $p$,
--   and since $S$ lies below $p/2$ and is progression-free, $s_x = s_y = s_z$. The mixed address is
--   marginally regular because each of its three mode words is inherited from a marginally regular
--   address, so it is a legitimate member of the ambient family, and it carries the common hash value.
--
--   Vertex closure is exactly the hypothesis the deterministic pruning step needs: it guarantees that a
--   supported mixed address of retained vertices is again a retained edge, so inducedness can be
--   certified inside the retained family.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, proof of Lemma 3.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_affine_hash
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.ZMod.Basic

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_hash_retained_vertex_closed
    (base : Fin 10 → ℕ) (m p : ℕ) (S : Finset ℕ) (b0 : ZMod p)
    (w : Fin (MME.StothersFourth.genOuterLength base m) → ZMod p)
    (hpodd : Odd p)
    (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) :
    MME.StothersFourth.GenMarginalVertexClosed (MME.StothersFourth.genHashRetainedEdges base m p S b0 w) := by
  sorry
