-- Prove2me | Theorems.Thm_ProofsInTheBook_PlanarMap_PlaneSimpleGraph_fiveColor_planeSimpleGraph
-- name    : ProofsInTheBook.PlanarMap.PlaneSimpleGraph.fiveColor_planeSimpleGraph
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T19:49:26.668231+00:00
-- url     : https://prove2.me/theorems/5c795937-177f-4cc3-b78e-9f6cf98cfaad
-- title:
--   Five-coloring connected sphere rotation systems with incident vertices and face length at least three
-- statement:
--   Let $V,D$ be finite sets with decidable equality, with $D\ne\varnothing$. Let $G$ be a connected simple graph on $V$. Suppose a dart representation consists of maps $t,h:D\to V$ and permutations $\alpha,\sigma$ of $D$ satisfying: $\alpha^2=\mathrm{id}$; $\alpha(d)\ne d$ for every dart; $t(\alpha(d))=h(d)$ and $h(\alpha(d))=t(d)$; each dart joins adjacent vertices of $G$; and for every ordered adjacent pair $(u,v)$ there is exactly one dart $d$ with $t(d)=u$ and $h(d)=v$. Also assume $t(\sigma(d))=t(d)$ and that any two darts with the same tail lie in the same $\sigma$-orbit. These are the fields of PlaneSimpleGraph; connectedness is a required field, not supplied by the name alone.
--
--   Put $\varphi=\sigma\circ\alpha$, let $f$ be the number of $\varphi$-orbits, and let $e=|D|/2$ (natural-number division; the fixed-point-free involution pairs the darts). Assume the sphere condition, the incidence condition, and the face-length condition:
--   $$|V|-e+f=2,\qquad\forall v\in V,\ \exists d\in D,\ t(d)=v,\qquad\forall O\in D/\langle\varphi\rangle,\ |O|\ge3.$$
--   The Euler equality is in the integers. The incidence condition excludes isolated vertices; the face-length condition covers every face, including any face subsequently designated as outer. Then there exists a coloring $c:V\to\{0,1,2,3,4\}$ such that
--   $$\forall u,v\in V,\quad G(u,v)\Longrightarrow c(u)\ne c(v).$$
--   This result supplies the triangulation extension internally, but retains the stated connectedness, nonempty dart set, incidence, sphere, and face-length inputs. It is not a declaration for all abstract planar graphs without those inputs.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlaneSimpleGraphTriangulate.lean#L1225 (headline); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlaneSimpleGraph.lean#L17 (all graph and dart fields); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlaneSimpleGraph.lean#L64 (sphere condition); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapEuler.lean#L23 (face length). Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 39, “Five-coloring plane graphs”, pp. 277–280 (https://doi.org/10.1007/978-3-662-57265-8_39).

import Init
import Mathlib
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
import Definitions.Def_P2MAssembly_Chapter35Plane

set_option autoImplicit true
set_option autoImplicit true
set_option linter.unusedSectionVars false
open ProofsInTheBook.PlanarMap
open Equiv
universe u v u'
open ProofsInTheBook.PlanarMap.PlaneSimpleGraph
variable {V : Type v} {D : Type u} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

theorem ProofsInTheBook.PlanarMap.PlaneSimpleGraph.fiveColor_planeSimpleGraph (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v)
    (h3 : P.toCombMap.FaceLengthGe 3)
    [Nonempty D] :
    P.G.Colorable 5 := by sorry
