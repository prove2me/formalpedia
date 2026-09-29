-- Prove2me | Definitions.Def_Kepler_LPGeometricVariables
-- name    : Kepler_LPGeometricVariables
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T02:56:35.776928+00:00
-- url     : https://prove2.me/theorems/ad2f72e4-c329-4dd0-b08e-329f74a53450
-- title:
--   Geometric meanings of LP variables
-- statement:
--   The ambient space is Euclidean $\mathbb R^3$. A finite hypermap $H$ consists of a natural number $d$, darts $\{0,\ldots,d-1\}$ and permutations $e,n,f$ with $e(n(f(a)))=a$ for every dart. Let $E_a,N_a,F_a$ be its edge, node and face permutation-cycle orbits, including $a$, and let $\mathcal E,\mathcal N,\mathcal F$ be the finite sets of distinct such orbits. Let $\mathcal K$ be the finite set of distinct components reachable by zero or more applications of $e,n,f$. Incident faces at $a$ are the distinct sets $\mathcal I_a=\{F_b:b\in N_a\}$. Write $\mathcal T_a,\mathcal Q_a,\mathcal X_a$ for those incident faces of size $3$, size $4$, and size at least $5$, respectively, and $(p_a,q_a,x_a)=(|\mathcal T_a|,|\mathcal Q_a|,|\mathcal X_a|)$. A face list $L$ is a finite ordered list of finite lists of natural labels. A face $[v_0,\ldots,v_{k-1}]$ supplies the cyclic directed pairs $(v_i,v_{i+1\bmod k})$; an empty face supplies none, and a singleton supplies a loop. The dart list concatenates these lists with multiplicities. Good means no repeated directed pair, every face nonempty, and each occurring $(u,v)$ accompanied by $(v,u)$; it imposes no further length, label-range, connectedness or planarity condition, and the empty list is Good. The list represents $H$ if $e^2=\mathrm{id}$ and there exists a labeling $\ell$ of darts by natural numbers such that $\ell(a)=\ell(b)\Leftrightarrow b\in N_a$, the map $a\mapsto(\ell(a),\ell(f(a)))$ is injective, $(\ell(e(a)),\ell(f(e(a))))=(\ell(f(a)),\ell(a))$, every face of $L$ is a cyclic rotation of $[\ell(a),\ell(f(a)),\ldots,\ell(f^{|F_a|-1}(a))]$ for some dart $a$, and every dart has such a face in $L$. Representation alone permits repeating a face. The opposite hypermap has the same darts and permutations $f\circ n,n^{-1},f^{-1}$. For an arbitrary placement $p$ of the darts in $\mathbb R^3$, the representation-label function is one fixed classically chosen witnessing labeling when $L$ represents $H$, and the constant-zero labeling otherwise. For any labeling whatsoever, its labeled-position lookup at natural label $v$ returns $p(a)$ at the least dart number $a$ with that label, or the zero vector if none exists. Reflection negates coordinate $0$ and keeps coordinates $1,2$. For $L,H,p$, the position map $q:\mathbb N\to\mathbb R^3$ is chosen as follows. If $L$ represents $H$, choose a witnessing labeling and return $p(a)$ for the first dart, in the order $0,\ldots,d-1$, with label $v$, or $0$ if the label is missing. If this representation fails but $L$ represents the opposite, choose a labeling for the opposite and negate the first Cartesian coordinate of the same first-dart lookup in $p$. If neither representation holds return $0$ for every label. The direct representation takes priority if both hold. These are fixed choices, not universal quantification over all representing labelings. For $a,u,v\in\mathbb R^3$ put $P_a(u)=u-\langle u,a\rangle a/\|a\|^2$, using total division, and let $\theta$ be the unoriented Euclidean angle between $P_a(u)$ and $P_a(v)$. Define $Z(a,u,v)=0$ if $a=0$ or either projection is zero; otherwise it is $2\pi-\theta$ when $\det(a,u,v)<0$ and $\theta$ otherwise, including zero determinant with nonzero projections. A variable is a node-kind and natural label, a dart-kind and ordered pair of natural labels, or a face-kind and ordered finite list of such pairs. The following evaluation is defined for every face list $L'$ and every map $q:\mathbb N\to\mathbb R^3$, whether or not they arise from a representation. For a face list $L'$ and pair $a=(u,v)$, take the pair-list of the first face containing $a$, defaulting to the empty list. Let $a^+,a^-$ be its next and previous pairs at the first occurrence of $a$, defaulting to $a$ if lookup fails, and let $a^{--}=(a^-)^-$. Put $z_a=Z(q(u),q(v),q((a^-)_1))$, $s_0=3\arccos(1/3)-\pi$, $\lambda(t)=(63-25t)/13$ for $t\leq63/25$ and $0$ otherwise, and $R_v=1+(s_0/\pi)(1-\lambda(\|q(v)\|))$. Node variables yn, ln, rho evaluate to $\|q(v)\|,\lambda(\|q(v)\|),|R_v|$. Dart variables azim, azim2, azim3 evaluate to $z_a,z_{a^+},z_{a^-}$; rhazim, rhazim2, rhazim3 evaluate to $|R_{a_1}|z_a,|R_{(a^+)_1}|z_{a^+},|R_{(a^-)_1}|z_{a^-}$. Dart variables ye and y6 both give $\|q(u)-q(v)\|$; y1,y2,y3 give $\|q(u)\|,\|q(v)\|,\|q((a^-)_1)\|$; y4 and y9 both give the length of $a^+$; y5 gives the length of $a^-$; y7 gives $\|q((a^{--})_1)\|$; y8 gives the length of $a^{--}$; and y4prime gives $\|q(v)-q((a^-)_1)\|$. For a pair-list $F$, its face sol variable is $|\sum_{a\in F}(z_a-\pi)+2\pi|$, and its tau variable is $|\sum_{a\in F}z_aR_{a_1}+(\pi+s_0)(2-|F|)|$, counting list multiplicities. A node address is valid if its label occurs in $L'$. For dart kinds ye,y1,y2,y6, both endpoint labels must occur but the pair need not; all other dart kinds require the pair itself in the dart list. A face address must equal an occurring face's pair-list exactly, not just up to rotation. The complete node kinds are yn, ln and rho; the complete face kinds are sol and tau; the complete dart kinds are precisely those just listed. List order and repeated pairs affect these functions. Evaluating a variable does not test its address predicate. In particular all missing-dart lookups use the stated fallback, the empty face has sol value $2\pi$ and tau value $|2(\pi+s_0)|$, and empty hypermaps and face lists remain permitted inputs. Decidability of the address predicate supplies a yes/no test for that predicate and no additional geometric assertion.
--
--   **Source and scope.** Primary §9; final formal_lp/hypermap/ineqs/lp_ineqs_defs.hl. Fixed node, dart and face evaluations, including the source absolute-value conventions and opposite-orientation reflection.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §9; final formal_lp/hypermap/ineqs/lp_ineqs_defs.hl. Fixed node, dart and face evaluations, including the source absolute-value conventions and opposite-orientation reflection.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

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
import Definitions.Def_Kepler_TameArchive
import Definitions.Def_Kepler_GeometricRealization
import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace KeplerMission.SourceLP

/-- Choose only the node-label witness already present in archive representation.
The fallback is used outside the represented domain and asserts no fact. -/
noncomputable def representationLabels (L : FaceList) (H : FiniteHypermap) :
    Fin H.dartCount → ℕ := by
  classical
  exact if h : L.Represents H then Classical.choose h.2 else fun _ ↦ 0

/-- Fixed first-dart lookup for a node label, with zero at unused labels. -/
def labeledPosition (H : FiniteHypermap) (p : GeometricPlacement H)
    (labels : Fin H.dartCount → ℕ) (v : ℕ) : Space :=
  match (List.finRange H.dartCount).find? (fun d ↦ labels d = v) with
  | some d => p d
  | none => 0

/-- Reflection of coordinate zero, used when the archive represents the opposite
orientation. It preserves lengths and reverses three-dimensional orientation. -/
def reflectPosition (v : Space) : Space :=
  WithLp.toLp 2 (fun i : Fin 3 ↦ if i = 0 then -(v i) else v i)

/-- Fixed source coordinate assignment. Direct representation has priority; otherwise
an opposite representation is reflected. No freely chosen LP assignment is a field. -/
noncomputable def sourcePosition (L : FaceList) (H : FiniteHypermap)
    (p : GeometricPlacement H) (v : ℕ) : Space := by
  classical
  exact if L.Represents H then labeledPosition H p (representationLabels L H) v
    else if L.Represents H.opposite then
      reflectPosition (labeledPosition H p (representationLabels L H.opposite) v)
    else 0

/-- The source ordered face containing an ordered dart. Empty outside valid addresses. -/
def faceDartsOf (L : FaceList) (d : ℕ × ℕ) : List (ℕ × ℕ) :=
  ((L.map FaceList.faceDarts).find? (fun f ↦ d ∈ f)).getD []

/-- Cyclic successor on the explicitly selected face. -/
def nextDart (L : FaceList) (d : ℕ × ℕ) : ℕ × ℕ :=
  let f := faceDartsOf L d
  (f.rotate 1)[f.idxOf d]?.getD d

/-- Cyclic predecessor on the explicitly selected face. -/
def previousDart (L : FaceList) (d : ℕ × ℕ) : ℕ × ℕ :=
  let f := faceDartsOf L d
  (f.rotate (f.length - 1))[f.idxOf d]?.getD d

/-- Source `lp_ineqs_defs.hl` variable categories. -/
inductive NodeQuantity where
  | yn | ln | rho
  deriving DecidableEq, Repr

inductive DartQuantity where
  | azim | azim2 | azim3 | rhazim | rhazim2 | rhazim3
  | ye | y1 | y2 | y3 | y4 | y5 | y6 | y7 | y8 | y9 | y4prime
  deriving DecidableEq, Repr

inductive FaceQuantity where
  | sol | tau
  deriving DecidableEq, Repr

/-- Concrete addresses, not arbitrary real-valued functions or propositions. -/
inductive Variable where
  | node (kind : NodeQuantity) (v : ℕ)
  | dart (kind : DartQuantity) (d : ℕ × ℕ)
  | face (kind : FaceQuantity) (f : List (ℕ × ℕ))
  deriving DecidableEq, Repr

/-- Source `azim_dart`, restricted to the nondegenerate source face-list domain.
The orientation is from the next vertex to the previous vertex about the dart tail.
Any use as an LP variable must prove its source fan/address conditions. -/
noncomputable def dartAzimuth (L : FaceList) (p : ℕ → Space) (d : ℕ × ℕ) : ℝ :=
  geometricAzimuth (p d.1) (p d.2) (p (previousDart L d).1)

noncomputable def radialCoefficient (p : ℕ → Space) (v : ℕ) : ℝ :=
  1 + (regularTetrahedronSolidAngle / Real.pi) * (1 - sourceRadialWeight ‖p v‖)

/-- Source face solid angle and score, each with the source absolute value. -/
noncomputable def faceValue (L : FaceList) (p : ℕ → Space)
    (kind : FaceQuantity) (f : List (ℕ × ℕ)) : ℝ :=
  match kind with
  | .sol => |(f.map (fun d ↦ dartAzimuth L p d - Real.pi)).sum + 2 * Real.pi|
  | .tau => |(f.map (fun d ↦ dartAzimuth L p d * radialCoefficient p d.1)).sum +
      (Real.pi + regularTetrahedronSolidAngle) * (2 - (f.length : ℝ))|

noncomputable def nodeValue (p : ℕ → Space) : NodeQuantity → ℕ → ℝ
  | .yn, v => ‖p v‖
  | .ln, v => sourceRadialWeight ‖p v‖
  | .rho, v => |radialCoefficient p v|

noncomputable def dartValue (L : FaceList) (p : ℕ → Space)
    (kind : DartQuantity) (d : ℕ × ℕ) : ℝ :=
  let next := nextDart L d
  let prev := previousDart L d
  let prev₂ := previousDart L prev
  match kind with
  | .azim => dartAzimuth L p d
  | .azim2 => dartAzimuth L p next
  | .azim3 => dartAzimuth L p prev
  | .rhazim => |radialCoefficient p d.1| * dartAzimuth L p d
  | .rhazim2 => |radialCoefficient p next.1| * dartAzimuth L p next
  | .rhazim3 => |radialCoefficient p prev.1| * dartAzimuth L p prev
  | .ye | .y6 => dist (p d.1) (p d.2)
  | .y1 => ‖p d.1‖
  | .y2 => ‖p d.2‖
  | .y3 => ‖p prev.1‖
  | .y4 | .y9 => dist (p next.1) (p next.2)
  | .y5 => dist (p prev.1) (p prev.2)
  | .y7 => ‖p prev₂.1‖
  | .y8 => dist (p prev₂.1) (p prev₂.2)
  | .y4prime => dist (p d.2) (p prev.1)

noncomputable def Variable.eval (L : FaceList) (p : ℕ → Space) : Variable → ℝ
  | .node kind v => nodeValue p kind v
  | .dart kind d => dartValue L p kind d
  | .face kind f => faceValue L p kind f

/-- Row data must separately validate every address. Distances and endpoint norms
need only existing vertices; quantities using face maps require an actual dart.
Face sums refer to one complete ordered source face, with nodup supplied by Good. -/
def Variable.ValidAddress (L : FaceList) : Variable → Prop
  | .node _ v => v ∈ L.flatten
  | .dart .ye d | .dart .y1 d | .dart .y2 d | .dart .y6 d =>
      d.1 ∈ L.flatten ∧ d.2 ∈ L.flatten
  | .dart _ d => d ∈ L.darts
  | .face _ f => f ∈ L.map FaceList.faceDarts

instance (L : FaceList) (v : Variable) : Decidable (v.ValidAddress L) := by
  cases v with
  | node kind v => unfold Variable.ValidAddress; infer_instance
  | dart kind d => cases kind <;> unfold Variable.ValidAddress <;> infer_instance
  | face kind f => unfold Variable.ValidAddress; infer_instance

end KeplerMission.SourceLP


