-- Prove2me | Definitions.Def_Kepler_GeometricRealization
-- name    : Kepler_GeometricRealization
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T02:56:03.302496+00:00
-- url     : https://prove2.me/theorems/3439bbec-dc89-4e42-8217-8660624096b8
-- title:
--   Contravening geometric realizations
-- statement:
--   Work in Euclidean $\mathbb R^3$. A packing has distance at least $2$ between distinct members. Put $A=\{v:2\leq\|v\|\leq63/25\}$, $w(t)=(63-25t)/13$, and $S(s)=\sum_{v\in s}w(\|v\|)$ for finite sets $s$. A finite hypermap $H$ consists of a natural number $d$, darts $\{0,\ldots,d-1\}$ and permutations $e,n,f$ with $e(n(f(a)))=a$ for every dart. Let $E_a,N_a,F_a$ be its edge, node and face permutation-cycle orbits, including $a$, and let $\mathcal E,\mathcal N,\mathcal F$ be the finite sets of distinct such orbits. Let $\mathcal K$ be the finite set of distinct components reachable by zero or more applications of $e,n,f$. Incident faces at $a$ are the distinct sets $\mathcal I_a=\{F_b:b\in N_a\}$. Write $\mathcal T_a,\mathcal Q_a,\mathcal X_a$ for those incident faces of size $3$, size $4$, and size at least $5$, respectively, and $(p_a,q_a,x_a)=(|\mathcal T_a|,|\mathcal Q_a|,|\mathcal X_a|)$. The condition called tame requires $e^2=\mathrm{id}$; $|\mathcal N|+|\mathcal E|+|\mathcal F|=d+2|\mathcal K|$; $|\mathcal K|=1$; $N_a\cap F_a=\{a\}$ for every dart; $e(a)\neq a$; $b\in E_a\cap N_a\Rightarrow b=a$; $b\in N_a$ and $e(b)\in N_{e(a)}\Rightarrow b=a$; at least three distinct faces; $3\leq|F_a|\leq6$ and $3\leq|N_a|\leq7$ for every dart; $|\mathcal N|\in\{13,14,15\}$; and, whenever $|F_a|\geq5$, both $|N_a|\leq6$ and $|N_a|=6\Rightarrow(p_a,q_a,x_a)=(5,0,1)$. It further requires a real function $W$ on all finite subsets of the dart set with $W(F_a)\geq a_{|F_a|}$ for every dart, $\sum_{F\in\mathcal I_a}W(F)\geq b_{p_a,q_a}$ when $x_a=0$, $\sum_{F\in\mathcal T_a}W(F)\geq63/100$ when $(p_a,q_a,x_a)=(5,0,1)$, and $\sum_{F\in\mathcal F}W(F)<1541/1000$. The face constants are $a_3=0,a_4=206/1000,a_5=4819/10000,a_6=712/1000$, with $a_k=1541/1000$ otherwise. In the order $(p,q)=(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0),(7,0)$, the exceptional values of $b_{p,q}$ are $618/1000,97/100,656/1000,618/1000,797/1000,412/1000,12851/10000,311/1000,817/1000,347/1000,366/1000,4/100,1136/1000,686/1000,145/100$; every other pair has value $1541/1000$. Values of $W$ away from actual faces are unrestricted. An empty hypermap is a permitted structure but cannot be tame. For $a,u,v\in\mathbb R^3$ put $P_a(u)=u-\langle u,a\rangle a/\|a\|^2$, using total division, and let $\theta$ be the unoriented Euclidean angle between $P_a(u)$ and $P_a(v)$. Define $Z(a,u,v)=0$ if $a=0$ or either projection is zero; otherwise it is $2\pi-\theta$ when $\det(a,u,v)<0$ and $\theta$ otherwise, including zero determinant with nonzero projections. For a finite set $s$, standard neighbors of a member $v$ are $\{u\in s:u\neq v,\ \|u-v\|\leq63/25\}$, and contact neighbors are $\{u\in s:u\neq v,\ \|u-v\|=2\}$; a point outside $s$ has no neighbors. For either relation, the successor of $w$ around $v$ is $w$ if the neighbor set is exactly $\{w\}$; otherwise it is a chosen neighbor $u\neq w$ minimizing $Z(v,w,u)$ among neighbors other than $w$. If no such neighbor exists the choice has no specified property; minimizers need not be unique. The dart angle is $Z(v,w,\operatorname{successor}(v,w))$ when $v$ has more than one neighbor and $2\pi$ otherwise. Being surrounded means that membership in $s$ implies a nonempty neighbor set and a dart angle strictly less than $\pi$ at every neighbor. Outside $s$ this implication is vacuous. A contravening configuration is a finite set $s$ of pairwise separated points in the closed annulus $2\leq\|v\|\leq63/25$, with score $S(s)=\sum_{v\in s}(63-25\|v\|)/13>12$, and with score at least that of every finite packing in that annulus, without restricting competitors' cardinality. It must also have $13$, $14$ or $15$ members; every member must be surrounded for standard neighbors; and every member must either be surrounded for contact neighbors or have norm exactly $2$. A placement of $H$ is any map $p$ from darts into $\mathbb R^3$, with center set $s_p=\{p(a):a\text{ a dart}\}$, counting distinct images once. It realizes the standard fan when $p(a)=p(b)\Leftrightarrow b\in N_a$, each $p(e(a))$ is a standard neighbor of $p(a)$, every ordered standard-neighbor pair $(v,w)$ in $s_p$ comes from exactly one dart $a$ with $p(a)=v,p(e(a))=w$, $p(e(e(a)))=p(a)$, and $p(e(n(a)))$ equals the chosen standard successor of $p(e(a))$ around $p(a)$. A contravening realization is a standard-fan realization whose center set is a contravening configuration; it does not additionally assume tameness or an involutive edge permutation on darts. A realization dart angle is its standard-fan dart angle. Its face weight at dart $d$ is the signed quantity $\sum_{a\in F_d}\theta_a[1+(s_0/\pi)(1-\lambda(\|p(a)\|))]+(\pi+s_0)(2-|F_d|)$, where $s_0=3\arccos(1/3)-\pi$ and $\lambda(t)=w(t)$ for $t\leq63/25$ and $0$ otherwise. This is a signed value, with no absolute value. Contravention extraction means that existence of any finite packing in the annulus with score strictly greater than $12$ implies existence of a contravening configuration, including its global score-maximality, cardinality and surrounding conditions. Tame realization means that for every contravening configuration $s$ there exist a finite hypermap $H$ and placement $p$ whose image center set is exactly $s$, which realizes the standard fan and for which $H$ satisfies all the tame requirements. The existential hypermap and placement may depend on $s$, with no uniqueness, canonical labels or separate prescribed weight function. All the displayed geometry functions are total: division by zero is $0$, so $P_0(u)=u$, while the azimuth definition explicitly returns $0$ when its axis is zero. The extraction and realization statements are defined propositions, with implications vacuous when their stated counterexample hypotheses have no witness; the bundle does not assert that either proposition holds.
--
--   **Source and scope.** Primary §4.2 pp.8–10 and §§7–8; Blueprint Theorem8.41; FCDJDOT/YXISOKH/MQMSMAB. Unchanged local configurations, standard-fan realization and extraction interfaces.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §4.2 pp.8–10 and §§7–8; Blueprint Theorem8.41; FCDJDOT/YXISOKH/MQMSMAB. Unchanged local configurations, standard-fan realization and extraction interfaces.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

/-
Flyspeck source material is reproduced and adapted under this license:
MIT License

Copyright (c) 2014 Thomas C. Hales

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Definitions.Def_Kepler_PackingModel
import Definitions.Def_Kepler_TameArchive
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

set_option autoImplicit false

open scoped BigOperators

namespace KeplerMission

/-- Projection onto the plane perpendicular to `axis`, as in `Sphere.projection`.
The relevant annulus axes have norm at least 2. -/
noncomputable def axisProjection (axis v : Space) : Space :=
  v - ((∑ i, v i * axis i) / (∑ i, axis i ^ 2)) • axis

/-- The oriented scalar triple product in the standard orientation of real three-space. -/
def scalarTriple (u v w : Space) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
    u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- Azimuth about the ray through `axis`, using values in `[0, 2π)`. Degenerate
triples return zero, as in HOL Light `Multivariate/flyspeck.ml:azim_def`. -/
noncomputable def geometricAzimuth (axis u v : Space) : ℝ := by
  classical
  let uperp := axisProjection axis u
  let vperp := axisProjection axis v
  let a := InnerProductGeometry.angle uperp vperp
  exact if axis = 0 ∨ uperp = 0 ∨ vperp = 0 then 0
    else if scalarTriple axis u v < 0 then 2 * Real.pi - a else a

inductive FanEdgeKind where
  | standard
  | contact
  deriving DecidableEq

/-- `ESTD` and `ECTC` neighbors: standard edges have length at most 2.52;
contact edges have length exactly 2. Source: `tame/tame_defs.hl`. -/
noncomputable def fanNeighbors (s : Finset Space) (kind : FanEdgeKind) (v : Space) :
    Finset Space := by
  classical
  exact if v ∈ s then s.filter (fun w ↦ w ≠ v ∧ match kind with
    | .standard => dist v w ≤ (63 : ℝ) / 25
    | .contact => dist v w = 2) else ∅

/-- Exact finite-set form of `fan/fan_defs.hl:sigma_fan`: minimum azimuth among
other neighbors, with a singleton exception. Choice does not assert any estimate. -/
noncomputable def fanSuccessor (s : Finset Space) (kind : FanEdgeKind)
    (v w : Space) : Space := by
  classical
  let neighbors := fanNeighbors s kind v
  exact if neighbors = {w} then w else Classical.epsilon fun u ↦
    u ∈ neighbors ∧ u ≠ w ∧
      ∀ q ∈ neighbors, q ≠ w → geometricAzimuth v w u ≤ geometricAzimuth v w q

/-- `fan/fan_defs.hl:azim_fan`; a node with at most one neighbor has full-turn angle. -/
noncomputable def fanDartAzimuth (s : Finset Space) (kind : FanEdgeKind)
    (v w : Space) : ℝ := by
  classical
  exact if 1 < (fanNeighbors s kind v).card then
    geometricAzimuth v w (fanSuccessor s kind v w) else 2 * Real.pi

/-- Finite form of `Tame_defs.surrounded_node`. The isolated-node dart has angle 2π,
so the source predicate is false at an isolated center and vacuous outside `s`. -/
def SurroundedNode (s : Finset Space) (kind : FanEdgeKind) (v : Space) : Prop :=
  v ∈ s → (fanNeighbors s kind v).Nonempty ∧
    ∀ w ∈ fanNeighbors s kind v, fanDartAzimuth s kind v w < Real.pi

noncomputable def annulusScore (s : Finset Space) : ℝ :=
  ∑ v ∈ s, annulusWeight ‖v‖

/-- Source `Tame_defs.contravening`; Blueprint FCDJDOT/YXISOKH. This describes a
maximizing local counterexample, not a packing structure or an assumed impossibility. -/
def ContraveningConfiguration (s : Finset Space) : Prop :=
  IsPacking (s : Set Space) ∧ (↑s : Set Space) ⊆ annulus ∧ 12 < annulusScore s ∧
    (∀ t : Finset Space, IsPacking (t : Set Space) → (↑t : Set Space) ⊆ annulus →
      annulusScore t ≤ annulusScore s) ∧
    (s.card = 13 ∨ s.card = 14 ∨ s.card = 15) ∧
    (∀ v ∈ s, SurroundedNode s .standard v) ∧
    (∀ v ∈ s, SurroundedNode s .contact v ∨ ‖v‖ = 2)


/-- Node positions are ordinary Euclidean coordinates; validity is a separate predicate. -/
abbrev GeometricPlacement (H : FiniteHypermap) := Fin H.dartCount → Space

noncomputable def realizationCenters (H : FiniteHypermap) (p : GeometricPlacement H) :
    Finset Space := by
  classical
  exact Finset.univ.image p

/-- Explicit realization of `hypermap_of_fan (V, ESTD V)` on a finite dart carrier.
Darts are in bijection with directed short edges, node cycles follow geometric azimuth,
and the edge permutation reverses each directed edge. No estimate is a structure field. -/
def RealizesStandardFan (H : FiniteHypermap) (p : GeometricPlacement H) : Prop :=
  (∀ d e, p d = p e ↔ e ∈ H.nodeOrbit d) ∧
    (∀ d, p (H.edge d) ∈ fanNeighbors (realizationCenters H p) .standard (p d)) ∧
    (∀ v ∈ realizationCenters H p,
      ∀ w ∈ fanNeighbors (realizationCenters H p) .standard v,
        ∃! d, p d = v ∧ p (H.edge d) = w) ∧
    (∀ d, p (H.edge (H.edge d)) = p d) ∧
    (∀ d, p (H.edge (H.node d)) =
      fanSuccessor (realizationCenters H p) .standard (p d) (p (H.edge d)))

/-- The concrete configuration space associated to an oriented archive hypermap.
Blueprint Chapter 8, Linear Programs, `CalV_H`; orientation is handled by the archive
obligation using both a hypermap and its opposite. -/
def ContraveningRealization (H : FiniteHypermap) (p : GeometricPlacement H) : Prop :=
  RealizesStandardFan H p ∧ ContraveningConfiguration (realizationCenters H p)

noncomputable def realizationDartAngle (H : FiniteHypermap) (p : GeometricPlacement H)
    (d : Fin H.dartCount) : ℝ :=
  fanDartAzimuth (realizationCenters H p) .standard (p d) (p (H.edge d))

/-- `Pack_defs.sol0`, the solid angle of a regular tetrahedron. -/
noncomputable def regularTetrahedronSolidAngle : ℝ :=
  3 * Real.arccos (1 / 3) - Real.pi

/-- `Pack_defs.lmfun (t/2)`, including the source cutoff outside the annulus. -/
noncomputable def sourceRadialWeight (t : ℝ) : ℝ := by
  classical
  exact if t ≤ (63 : ℝ) / 25 then annulusWeight t else 0

/-- Exact `Tame_defs.tauVEF` sum on a represented face orbit. -/
noncomputable def realizationFaceWeight (H : FiniteHypermap) (p : GeometricPlacement H)
    (d : Fin H.dartCount) : ℝ :=
  (∑ a ∈ H.faceOrbit d, realizationDartAngle H p a *
    (1 + (regularTetrahedronSolidAngle / Real.pi) * (1 - sourceRadialWeight ‖p a‖))) +
    (Real.pi + regularTetrahedronSolidAngle) * (2 - ((H.faceOrbit d).card : ℝ))

/-- Source extraction lemma FCDJDOT, recorded as an unproved proposition type. -/
def ContraventionExtractionStatement : Prop :=
  (∃ s : Finset Space, IsPacking (s : Set Space) ∧ (↑s : Set Space) ⊆ annulus ∧
    12 < annulusScore s) → ∃ s : Finset Space, ContraveningConfiguration s

/-- Source `MQMSMAB`: a contravening configuration has a tame standard-fan hypermap.
The nonlinear estimates needed for a proof belong in the milestone dependencies. -/
def TameRealizationStatement : Prop :=
  ∀ s : Finset Space, ContraveningConfiguration s →
    ∃ (H : FiniteHypermap) (p : GeometricPlacement H),
      realizationCenters H p = s ∧ RealizesStandardFan H p ∧ H.IsTame

end KeplerMission


