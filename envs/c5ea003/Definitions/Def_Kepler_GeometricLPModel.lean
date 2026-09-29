-- Prove2me | Definitions.Def_Kepler_GeometricLPModel
-- name    : Kepler_GeometricLPModel
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T03:12:19.456909+00:00
-- url     : https://prove2.me/theorems/b9f0b000-3a02-48cd-ace3-305df312b439
-- title:
--   Contravening geometry and fixed final LP family
-- statement:
--   The ambient space is $\mathbb R^3$ with its Euclidean norm and distance. A set $V$ is a packing exactly when distinct members have distance at least $2$, with no nonemptiness or saturation requirement. Write $B(a,r)=\{x:\|x-a\|<r\}$ and $N_V(a,r)=\#(V\cap B(a,r))$, where this natural-number cardinality is defined as $0$ if the intersection is infinite. Put $w(t)=(63/25-t)/(63/25-2)=(63-25t)/13$, $A=\{x:2\leq\|x\|\leq63/25\}$ and $S(s)=\sum_{v\in s}w(\|v\|)$ for finite sets $s$. Saturation means $\forall x\in\mathbb R^3\,\exists v\in V,\ \|x-v\|<2$; it alone does not require separation. The finite-container condition on $V$ is $\exists c\in\mathbb R\,\forall r\geq1,\ N_V(0,r)\leq\pi r^3/\sqrt{18}+cr^2$. The constant may depend on $V$ and has no sign restriction. A finite hypermap $H$ consists of a natural number $d$, darts $\{0,\ldots,d-1\}$ and permutations $e,n,f$ with $e(n(f(a)))=a$ for every dart. Let $E_a,N_a,F_a$ be its edge, node and face permutation-cycle orbits, including $a$, and let $\mathcal E,\mathcal N,\mathcal F$ be the finite sets of distinct such orbits. Let $\mathcal K$ be the finite set of distinct components reachable by zero or more applications of $e,n,f$. Incident faces at $a$ are the distinct sets $\mathcal I_a=\{F_b:b\in N_a\}$. Write $\mathcal T_a,\mathcal Q_a,\mathcal X_a$ for those incident faces of size $3$, size $4$, and size at least $5$, respectively, and $(p_a,q_a,x_a)=(|\mathcal T_a|,|\mathcal Q_a|,|\mathcal X_a|)$. The condition called tame requires $e^2=\mathrm{id}$; $|\mathcal N|+|\mathcal E|+|\mathcal F|=d+2|\mathcal K|$; $|\mathcal K|=1$; $N_a\cap F_a=\{a\}$ for every dart; $e(a)\neq a$; $b\in E_a\cap N_a\Rightarrow b=a$; $b\in N_a$ and $e(b)\in N_{e(a)}\Rightarrow b=a$; at least three distinct faces; $3\leq|F_a|\leq6$ and $3\leq|N_a|\leq7$ for every dart; $|\mathcal N|\in\{13,14,15\}$; and, whenever $|F_a|\geq5$, both $|N_a|\leq6$ and $|N_a|=6\Rightarrow(p_a,q_a,x_a)=(5,0,1)$. It further requires a real function $W$ on all finite subsets of the dart set with $W(F_a)\geq a_{|F_a|}$ for every dart, $\sum_{F\in\mathcal I_a}W(F)\geq b_{p_a,q_a}$ when $x_a=0$, $\sum_{F\in\mathcal T_a}W(F)\geq63/100$ when $(p_a,q_a,x_a)=(5,0,1)$, and $\sum_{F\in\mathcal F}W(F)<1541/1000$. The face constants are $a_3=0,a_4=206/1000,a_5=4819/10000,a_6=712/1000$, with $a_k=1541/1000$ otherwise. In the order $(p,q)=(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0),(7,0)$, the exceptional values of $b_{p,q}$ are $618/1000,97/100,656/1000,618/1000,797/1000,412/1000,12851/10000,311/1000,817/1000,347/1000,366/1000,4/100,1136/1000,686/1000,145/100$; every other pair has value $1541/1000$. Values of $W$ away from actual faces are unrestricted. An empty hypermap is a permitted structure but cannot be tame. A face list $L$ is a finite ordered list of finite lists of natural labels. A face $[v_0,\ldots,v_{k-1}]$ supplies the cyclic directed pairs $(v_i,v_{i+1\bmod k})$; an empty face supplies none, and a singleton supplies a loop. The dart list concatenates these lists with multiplicities. Good means no repeated directed pair, every face nonempty, and each occurring $(u,v)$ accompanied by $(v,u)$; it imposes no further length, label-range, connectedness or planarity condition, and the empty list is Good. The list represents $H$ if $e^2=\mathrm{id}$ and there exists a labeling $\ell$ of darts by natural numbers such that $\ell(a)=\ell(b)\Leftrightarrow b\in N_a$, the map $a\mapsto(\ell(a),\ell(f(a)))$ is injective, $(\ell(e(a)),\ell(f(e(a))))=(\ell(f(a)),\ell(a))$, every face of $L$ is a cyclic rotation of $[\ell(a),\ell(f(a)),\ldots,\ell(f^{|F_a|-1}(a))]$ for some dart $a$, and every dart has such a face in $L$. Representation alone permits repeating a face. The opposite hypermap has the same darts and permutations $f\circ n,n^{-1},f^{-1}$. The fixed archive has $19{,}715$ strings; decoding splits at periods into nonempty faces and maps A through O to labels $0$ through $14$. Empty strings, empty faces and other characters fail. Membership means equality to the decoded face list at some in-range index. Archive well-formedness requires successful decoding and Good at every index. For $a,u,v\in\mathbb R^3$ put $P_a(u)=u-\langle u,a\rangle a/\|a\|^2$, using total division, and let $\theta$ be the unoriented Euclidean angle between $P_a(u)$ and $P_a(v)$. Define $Z(a,u,v)=0$ if $a=0$ or either projection is zero; otherwise it is $2\pi-\theta$ when $\det(a,u,v)<0$ and $\theta$ otherwise, including zero determinant with nonzero projections. For a finite set $s$, standard neighbors of a member $v$ are $\{u\in s:u\neq v,\ \|u-v\|\leq63/25\}$, and contact neighbors are $\{u\in s:u\neq v,\ \|u-v\|=2\}$; a point outside $s$ has no neighbors. For either relation, the successor of $w$ around $v$ is $w$ if the neighbor set is exactly $\{w\}$; otherwise it is a chosen neighbor $u\neq w$ minimizing $Z(v,w,u)$ among neighbors other than $w$. If no such neighbor exists the choice has no specified property; minimizers need not be unique. The dart angle is $Z(v,w,\operatorname{successor}(v,w))$ when $v$ has more than one neighbor and $2\pi$ otherwise. Being surrounded means that membership in $s$ implies a nonempty neighbor set and a dart angle strictly less than $\pi$ at every neighbor. Outside $s$ this implication is vacuous. A contravening configuration is a finite set $s$ of pairwise separated points in the closed annulus $2\leq\|v\|\leq63/25$, with score $S(s)=\sum_{v\in s}(63-25\|v\|)/13>12$, and with score at least that of every finite packing in that annulus, without restricting competitors' cardinality. It must also have $13$, $14$ or $15$ members; every member must be surrounded for standard neighbors; and every member must either be surrounded for contact neighbors or have norm exactly $2$. A placement of $H$ is any map $p$ from darts into $\mathbb R^3$, with center set $s_p=\{p(a):a\text{ a dart}\}$, counting distinct images once. It realizes the standard fan when $p(a)=p(b)\Leftrightarrow b\in N_a$, each $p(e(a))$ is a standard neighbor of $p(a)$, every ordered standard-neighbor pair $(v,w)$ in $s_p$ comes from exactly one dart $a$ with $p(a)=v,p(e(a))=w$, $p(e(e(a)))=p(a)$, and $p(e(n(a)))$ equals the chosen standard successor of $p(e(a))$ around $p(a)$. A contravening realization is a standard-fan realization whose center set is a contravening configuration; it does not additionally assume tameness or an involutive edge permutation on darts. A realization dart angle is its standard-fan dart angle. Its face weight at dart $d$ is the signed quantity $\sum_{a\in F_d}\theta_a[1+(s_0/\pi)(1-\lambda(\|p(a)\|))]+(\pi+s_0)(2-|F_d|)$, where $s_0=3\arccos(1/3)-\pi$ and $\lambda(t)=w(t)$ for $t\leq63/25$ and $0$ otherwise. It has no absolute value, unlike the LP face coordinate. Contravention extraction means that existence of any finite packing in the annulus with score strictly greater than $12$ implies existence of a contravening configuration, including its global score-maximality, cardinality and surrounding conditions. Tame realization means that for every contravening configuration $s$ there exist a finite hypermap $H$ and placement $p$ whose image center set is exactly $s$, which realizes the standard fan and for which $H$ satisfies all the tame requirements. The existential hypermap and placement may depend on $s$, with no uniqueness, canonical labels or separate prescribed weight function. For $L,H,p$, the position map $q:\mathbb N\to\mathbb R^3$ is chosen as follows. If $L$ represents $H$, choose a witnessing labeling and return $p(a)$ for the first dart, in the order $0,\ldots,d-1$, with label $v$, or $0$ if the label is missing. If this representation fails but $L$ represents the opposite, choose a labeling for the opposite and negate the first Cartesian coordinate of the same first-dart lookup in $p$. If neither representation holds return $0$ for every label. The direct representation takes priority if both hold. These are fixed choices, not universal quantification over all representing labelings. For a face list $L'$ and pair $a=(u,v)$, take the pair-list of the first face containing $a$, defaulting to the empty list. Let $a^+,a^-$ be its next and previous pairs at the first occurrence of $a$, defaulting to $a$ if lookup fails, and let $a^{--}=(a^-)^-$. Put $z_a=Z(q(u),q(v),q((a^-)_1))$, $s_0=3\arccos(1/3)-\pi$, $\lambda(t)=(63-25t)/13$ for $t\leq63/25$ and $0$ otherwise, and $R_v=1+(s_0/\pi)(1-\lambda(\|q(v)\|))$. Node variables yn, ln, rho evaluate to $\|q(v)\|,\lambda(\|q(v)\|),|R_v|$. Dart variables azim, azim2, azim3 evaluate to $z_a,z_{a^+},z_{a^-}$; rhazim, rhazim2, rhazim3 evaluate to $|R_{a_1}|z_a,|R_{(a^+)_1}|z_{a^+},|R_{(a^-)_1}|z_{a^-}$. Dart variables ye and y6 both give $\|q(u)-q(v)\|$; y1,y2,y3 give $\|q(u)\|,\|q(v)\|,\|q((a^-)_1)\|$; y4 and y9 both give the length of $a^+$; y5 gives the length of $a^-$; y7 gives $\|q((a^{--})_1)\|$; y8 gives the length of $a^{--}$; and y4prime gives $\|q(v)-q((a^-)_1)\|$. For a pair-list $F$, its face sol variable is $|\sum_{a\in F}(z_a-\pi)+2\pi|$, and its tau variable is $|\sum_{a\in F}z_aR_{a_1}+(\pi+s_0)(2-|F|)|$, counting list multiplicities. A node address is valid if its label occurs in $L'$. For dart kinds ye,y1,y2,y6, both endpoint labels must occur but the pair need not; all other dart kinds require the pair itself in the dart list. A face address must equal an occurring face's pair-list exactly, not just up to rotation. A finite case tree is a leaf or a branch with an indexed child family. Its branch guards use $r_v=\|q(v)\|$ and $l_{uv}=\|q(u)-q(v)\|$. Rule 218 has children guarded by $109/50\leq r_v$ and $r_v\leq109/50$; rule 236 by $r_v\leq59/25$ and $59/25\leq r_v$; an edge rule by $9/4\leq l_{uv}$ and $l_{uv}\leq9/4$; a triangle rule by its perimeter being at least or at most $25/4$. For a quadrilateral set $a=l_{v_0v_2},b=l_{v_1v_3},t=\sqrt8$; its five guards are $a\leq b\land a\leq t$, $b\leq a\land b\leq t$, $a\leq b\land t\leq a\leq3$, $b\leq a\land t\leq b\leq3$, and $3\leq a\land3\leq b$. For a pentagon set $(a,b,c,d,e)=(l_{v_0v_2},l_{v_1v_3},l_{v_2v_4},l_{v_3v_0},l_{v_4v_1})$; its eleven guards are: all five at least $t$; $a\leq t\leq c,d$; $b\leq t\leq d,e$; $c\leq t\leq e,a$; $d\leq t\leq a,b$; $e\leq t\leq b,c$; $a,c\leq t$; $b,d\leq t$; $c,e\leq t$; $d,a\leq t$; and $e,b\leq t$. For a hexagon the six lengths are $l_{v_0v_2},l_{v_1v_3},l_{v_2v_4},l_{v_3v_5},l_{v_4v_0},l_{v_5v_1}$; its seven guards are all six at least $t$, followed by each individual length at most $t$. Rules high, mid and add_big each have one child with guard true. Reaching a leaf means a root-to-leaf path satisfying every guard; syntactic leaf membership ignores guards. Weak inequalities allow overlap at boundaries. The LP data are fixed tables of $19{,}715$ graph records, $43{,}078$ graph-indexed leaf records, $216$ selectable row names, and $1{,}525$ integer row templates at precisions $3$ through $7$. Graph identifier strings are not consulted. Tree decoding consumes space-separated tags l, 218, 236, edge, tri, quad, pent, hex, high, mid and add_big, their exact numbers of natural labels, and their prescribed numbers of children; malformed tokens, exhausted token-count fuel and leftovers fail. A tree starts with state $(L,\mathrm{true})$. Splitting a face at a pair finds the first containing face, rotates it so that the predecessor of the pair's initial label is first, then replaces a face longer than $3$ by its first three labels and by its first label followed by its labels from position $2$ onward. A shorter face is only rotated; no containing face leaves the list unchanged. Refinement marks the state false even if unchanged. Quad children $0,2$ refine at $(v_1,v_2)$, children $1,3$ at $(v_0,v_1)$, and child $4$ keeps the state. For pentagon and hexagon rules rotate their cyclic dart list once. Pentagon child $0$ keeps the state; children $1,\ldots,5$ refine at entries $0,\ldots,4$; children $6,\ldots,10$ split successively at those entries and the entries two positions later cyclically. Hexagon child $0$ keeps the state and children $1,\ldots,6$ refine at entries $0,\ldots,5$. Other rules leave the state unchanged. Leaves carry a natural ordinal and the accumulated state. A leaf code begins with a precision digit 3–7 and mode I or B, followed by vertical-bar-separated selections. Each selection starts with character code $256+k$ for an in-range name index, followed by i and indices encoded by characters # through p excluding backslash, giving $0,\ldots,76$, or by b and a base-64 bit mask in alphabet A–Z,a–z,0–9,-,_, with its first digit least significant. Only masks below $2^{77}$ pass; their set bits give indices. The stored graph index must equal the requested index. Template lookup selects the first matching name and precision, preferring a true standard-only flag in a true state and falling back to false; a false state only permits false. Index pools are distinct labels, all darts, all faces' dart lists, outgoing-dart lists for each distinct label, or darts of faces of a specified size. Distinct labels retain the order of last occurrences by right-to-left duplicate removal. Addresses select bound objects, all labels, next/previous/reversed darts, initial nodes, first darts or containing faces; feature constructors produce one coordinate or sum coordinates on a node/dart list. Type mismatches, empty required lookups and out-of-range pool indices fail. Each integer coefficient is copied to its instantiated terms, with no additional precision scaling. Selected row groups are concatenated. Mode I uses only them; mode B appends the false-flag main template at pool index $0$. Columns are the distinct syntactic variable addresses; a matrix entry sums every coefficient for that column in its row, and the right-hand side is the rational row constant. Compilation itself checks neither geometric validity nor nonempty rows, guards, feasibility or certificates. The archive obligation is a conjunction of three claims. First, the graph-table size is $19{,}715$, the leaf-table size $43{,}078$, and the graph-table size equals the decoded-archive size; for every archive index $i$ there are a successfully decoded list $L$ and successfully decoded state-labeled tree built from graph index $i$ and $L$, and every syntactic leaf location has a successfully compiled program with strictly positive row count and every column address valid in that location's face list. Second, for every index $i$, every list $L$ and tree satisfying those decoding equalities, every hypermap $H$ and placement $p$ with $L$ representing $H$ or its opposite and $(H,p)$ a contravening realization, and every location and successfully compiled program there, reaching that location under the radii and distances of the chosen map $q$ implies every row inequality $\sum_j A_{kj}x_j\leq b_k$ at the program's geometric column values, evaluated on that location's face list. Third, for every index, decoded list, decoded tree, syntactic leaf location and successfully compiled program there, a rational vector $y$ indexed by its rows exists such that $y_k\geq0$, $\sum_k y_kA_{kj}=0$ for each column, and $\sum_k y_kb_k<0$. The third claim includes geometrically unreachable leaves. It provides existential certificates rather than a displayed list of certificate vectors. The geometric implication can be vacuous in the absence of a contravening realization or guarded path, while successful compilation and certificates remain required at every syntactic leaf. For natural $m,n$, a rational system is any rational $m$-by-$n$ matrix $A$ and rational row vector of bounds $b$. A real vector $x$ is feasible precisely when $\sum_jA_{kj}x_j\leq b_k$ for every row. The Boolean infeasibility test decides $y\geq0$, $y^\mathsf TA=0$ and $y^\mathsf Tb<0$ for a rational row-indexed vector $y$. Its soundness proposition quantifies over all $m,n,A,b,y$ and says a true result rules out every feasible real vector. At $m=0$ the strict negative sum cannot hold; at $n=0$ there is one empty candidate vector and feasibility is $0\leq b_k$ in every row. Archived-case exclusion says no archived list represents a hypermap or opposite having a contravening realization. The assembly proposition says this exclusion follows from universal rational-certificate soundness and the three archive obligations. These are defined propositions, not facts supplied by constructing the data.
--
--   **Source and scope.** Primary §4.2 and §9, pp.8–10,21–24; final formal_lp/hypermap/verify_all.hl and main/prove_flyspeck_lp.hl:43–52,263–348,483–523,856–1037. All 19,715 source graph trees and 43,078 leaves are concrete data with 1,525 rounded integer templates. Local feasibility and exact certificate availability are distinct proof obligations.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §4.2 and §9, pp.8–10,21–24; final formal_lp/hypermap/verify_all.hl and main/prove_flyspeck_lp.hl:43–52,263–348,483–523,856–1037. All 19,715 source graph trees and 43,078 leaves are concrete data with 1,525 rounded integer templates. Local feasibility and exact certificate availability are distinct proof obligations.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

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
import Definitions.Def_Kepler_LPCaseModel
import Definitions.Def_Kepler_LPLeafModel

set_option autoImplicit false
open scoped BigOperators

namespace KeplerMission.SourceLP

/-- A concrete finite system. No fields contain propositions or proofs. -/
structure Program where
  rows : Array AffineRow

def Program.columns (p : Program) : Array Variable :=
  ((p.rows.toList.flatMap (fun row => row.terms.map Prod.snd)).dedup).toArray

def Program.system (p : Program) : RationalSystem p.rows.size p.columns.size where
  matrix i j := ((p.rows[i]).terms.map (fun (c, v) =>
    if v = p.columns[j] then c else 0)).sum
  rhs i := (p.rows[i]).rhs

noncomputable def Program.values (p : Program) (L : FaceList) (position : ℕ → Space) :
    Fin p.columns.size → ℝ := fun i => (p.columns[i]).eval L position

def Program.ValidAddresses (p : Program) (L : FaceList) : Prop :=
  ∀ v ∈ p.columns, v.ValidAddress L

abbrev Program.Certificate (p : Program) := Fin p.rows.size → ℚ

def Program.checkCertificate (p : Program) (cert : p.Certificate) : Bool :=
  p.system.checkInfeasibility cert

/-- The source objective cases append their separate score-lower-bound row.
The table stores its source scale 10^(3p). Direct infeasibility cases do not. -/
def compileProgram (state : CaseState) (spec : LeafSpecification) : Option Program := do
  let groups ← spec.selections.mapM (fun selection => do
    let template ← selectedTemplate state.standard spec.precision selection.nameIndex
    selection.indices.mapM (template.instantiate state.faces))
  let rows := groups.flatten
  if spec.directInfeasible then return ⟨rows.toArray⟩
  else
    let objective ← lookupTemplate false spec.precision "main"
    let scoreRow ← objective.instantiate state.faces 0
    return ⟨(rows ++ [scoreRow]).toArray⟩

/-- Resolve a source leaf ordinal with the graph binding checked before compilation. -/
def sourceProgram (graphIndex : ℕ) (location : LeafLocation) : Option Program := do
  let entry ← sourceLeafCodes[location.ordinal]?
  let spec ← decodeLeafSpecification entry
  if spec.graphIndex = graphIndex then compileProgram location.state spec else none

end KeplerMission.SourceLP


set_option autoImplicit false

namespace KeplerMission.SourceLP

/-- Unguarded structural leaf membership: even an unrealizable branch needs a certificate. -/
inductive SourceCaseTree.HasLeaf {α : Type} : SourceCaseTree α → α → Prop where
  | leaf (a : α) : HasLeaf (.leaf a) a
  | branch (rule : SplitRule) (children : Fin rule.arity → SourceCaseTree α)
      (i : Fin rule.arity) (a : α) (h : HasLeaf (children i) a) :
      HasLeaf (.branch rule children) a

def sourceTree (graphIndex : ℕ) (L : FaceList) : Option (SourceCaseTree LeafLocation) := do
  let code ← sourceGraphCodes[graphIndex]?
  let tree ← decodeCaseTree code.treeCode
  return tree.withState ⟨L, true⟩

/-- Pure data completeness, with no geometric conclusion or certificate hidden inside. -/
def FamilyWellFormed : Prop :=
  sourceGraphCodes.size = 19715 ∧ sourceLeafCodes.size = 43078 ∧
  sourceGraphCodes.size = tameArchiveEntries.size ∧
  ∀ i : Fin tameArchiveEntries.size,
    ∃ L tree, tameArchiveEntries[i] = some L ∧ sourceTree i.val L = some tree ∧
      ∀ location, tree.HasLeaf location → ∃ program,
        sourceProgram i.val location = some program ∧
        0 < program.rows.size ∧ program.ValidAddresses location.state.faces

/-- The sole geometric relaxation conclusion is feasibility of the fixed source LP.
The assignment is the declared geometric evaluator, never a solver-chosen vector. -/
def RelaxationsSound : Prop :=
  ∀ (i : Fin tameArchiveEntries.size) L tree,
    tameArchiveEntries[i] = some L → sourceTree i.val L = some tree →
    ∀ H (p : GeometricPlacement H),
      (L.Represents H ∨ L.Represents H.opposite) → ContraveningRealization H p →
      ∀ location program, sourceProgram i.val location = some program →
        tree.Reaches (fun v => ‖sourcePosition L H p v‖)
          (fun v w => dist (sourcePosition L H p v) (sourcePosition L H p w)) location →
        program.system.Feasible
          (program.values location.state.faces (sourcePosition L H p))

/-- Certificates are required for every fixed leaf independently of realizability. -/
def CertificatesAvailable : Prop :=
  ∀ (i : Fin tameArchiveEntries.size) L tree,
    tameArchiveEntries[i] = some L → sourceTree i.val L = some tree →
    ∀ location, tree.HasLeaf location → ∀ program,
      sourceProgram i.val location = some program →
      ∃ cert : program.Certificate, program.checkCertificate cert = true

def ArchiveContract : Prop :=
  FamilyWellFormed ∧ RelaxationsSound ∧ CertificatesAvailable

end KeplerMission.SourceLP


set_option autoImplicit false

namespace KeplerMission

/-- Generic arithmetic soundness, stated independently of any Kepler configuration. -/
def RationalCertificateSoundnessStatement : Prop :=
  ∀ (m n : ℕ) (S : RationalSystem m n) (y : Fin m → ℚ),
    S.checkInfeasibility y = true → ¬ ∃ x : Fin n → ℝ, S.Feasible x

/-- The fixed final Flyspeck case family, its local geometric relaxations, and
an exact rational certificate for every structural leaf. No case tree or LP can
be supplied by a solver: both are determined by the pinned source data. -/
abbrev LPArchiveObligations : Prop := SourceLP.ArchiveContract

/-- Source `linear_programming_results`, after its nonlinear/geometric inputs have
been proved: no contravening configuration realizes an archived combinatorial case. -/
def ArchivedCaseExclusionStatement : Prop :=
  ∀ L : FaceList, InTameArchive L → ∀ (H : FiniteHypermap) (p : GeometricPlacement H),
    (L.Represents H ∨ L.Represents H.opposite) → ¬ ContraveningRealization H p

/-- All-geometric case assembly target; its hypotheses are explicit interfaces. -/
def LPArchiveAssemblyStatement : Prop :=
  RationalCertificateSoundnessStatement → LPArchiveObligations → ArchivedCaseExclusionStatement

end KeplerMission


