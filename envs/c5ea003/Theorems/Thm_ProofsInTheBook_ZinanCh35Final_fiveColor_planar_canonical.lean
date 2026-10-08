-- Prove2me | Theorems.Thm_ProofsInTheBook_ZinanCh35Final_fiveColor_planar_canonical
-- name    : ProofsInTheBook.ZinanCh35Final.fiveColor_planar_canonical
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T19:42:53.264786+00:00
-- url     : https://prove2.me/theorems/73fbc010-5f71-461e-887c-9c4ceb8c6406
-- title:
--   Five-colorability of finite combinatorial near-triangulations
-- statement:
--   Let $D$ be a finite set with decidable equality. A combinatorial map on $D$ consists of permutations $\alpha,\sigma:D\to D$ with $\alpha^2=\mathrm{id}$ and $\alpha(d)\ne d$ for every $d\in D$. Put $\varphi=\sigma\circ\alpha$. Vertices, edges, and faces are respectively the orbits of $\sigma$, $\alpha$, and $\varphi$; write $V,E,F$ for their numbers. For each dart $d$, its tail is $[d]_\sigma$ and its head is $[\alpha(d)]_\sigma$. The associated simple graph has an edge between two distinct vertices precisely when some dart has those unordered endpoints. A face length is the number of darts in its $\varphi$-orbit.
--
--   Assume the supplied near-triangulation data have the following properties. The map is connected: every pair of darts can be joined by finitely many steps, each of which either stays in a $\sigma$-orbit or replaces $d$ by $\alpha(d)$. Its integer Euler characteristic is $V-E+F=2$. The map has no loops, meaning $[d]_\sigma\ne[\alpha(d)]_\sigma$ for every dart, and no parallel edges, meaning any two darts with the same unordered vertex endpoints lie in the same $\alpha$-orbit. There is a distinguished face $f_\infty$ with a chosen root and a nonempty cyclic dart list, without repetitions, enumerating exactly that face orbit and advancing by $\varphi$. Its induced tail-vertex list has no repetitions and has length at least three. Every other face has length exactly three. The boundary data also include the following certificate for every pair of distinct vertices $u,v$ in the distinguished boundary list: there are simple vertex lists from $u$ to $v$ and from $v$ to $u$, with all entries on the boundary, together covering the boundary vertices and having disjoint interior vertex lists. Each list has an interior vertex whenever the unordered pair $\{u,v\}$ is not one of the boundary edges. The certificate includes edge lists as part of its path data; the path structure does not independently impose an adjacency relation between those edge lists and consecutive vertices. Then the associated simple graph has a proper coloring with five colors. Equivalently, there exists $c:D/\langle\sigma\rangle\to\{0,1,2,3,4\}$ such that
--   $$\forall d\in D,\qquad c([d]_\sigma)\ne c([\alpha(d)]_\sigma).$$
--   The input is the specified finite near-triangulation map, including its boundary certificate. Isolated vertices are not separately represented: every vertex is a dart orbit and, under the no-loop hypothesis, is incident to an edge with a distinct other endpoint. The declaration does not quantify over arbitrary planar graphs or provide their augmentation to near-triangulations.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/ZinanCh35Final.lean#L257 (headline); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMap.lean#L24 (map); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMap.lean#L70 (connectedness); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMap.lean#L76 (sphere condition); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapSimple.lean#L82 (associated graph); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapSimple.lean#L97 (simplicity); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapEuler.lean#L23 (face length); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapBoundary.lean#L130 (boundary core); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapBoundary.lean#L161 (boundary certificate); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapNearTriangulation.lean#L21 (near-triangulation). Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 39, “Five-coloring plane graphs”, pp. 277–280 (https://doi.org/10.1007/978-3-662-57265-8_39).

import Init
import Mathlib
import Mathlib.Data.Finset.Basic
import Definitions.Def_P2MAssembly_Chapter35Canonical

set_option autoImplicit true
set_option autoImplicit true
set_option linter.unusedSectionVars false
open ProofsInTheBook.ZinanCh35Final
open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ZinanCh35Dichotomy
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35ChordlessOracle
universe u
variable {α : Type u} [DecidableEq α]

theorem ProofsInTheBook.ZinanCh35Final.fiveColor_planar_canonical
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M) :
    M.toSimpleGraph.Colorable 5 := by sorry
