-- Prove2me | Definitions.Def_Kepler_LPCaseModel
-- name    : Kepler_LPCaseModel
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T03:00:14.235898+00:00
-- url     : https://prove2.me/theorems/08daf6eb-f93f-4497-a574-0a00f38b709e
-- title:
--   Fixed case forest and face-refinement states
-- statement:
--   The graph-code array is the ordered concatenation of two fixed blocks with $13{,}250$ and $6{,}465$ records, hence $19{,}715$ records. Each record is a pair of arbitrary strings called graph identifier and tree code; this concatenation does not interpret them. A face list $L$ is any finite ordered list of finite lists of natural labels, whose face $[v_0,\ldots,v_{k-1}]$ gives cyclic directed pairs $(v_i,v_{i+1\bmod k})$, with an empty face giving no pairs and a singleton giving a loop. To split $L$ at a directed pair $d$, scan for the first face containing $d$, leaving all preceding and following faces in their original order. If no face contains it, leave $L$ unchanged. In the first containing face $f$, let $i$ be the first index of $d$ in its cyclic dart list, and rotate the vertex list left by $i$ and then left by $|f|-1$, putting the predecessor of $d$'s first vertex first. If the rotated list has at most three vertices, replace $f$ by this rotated list alone. Otherwise replace it, in order, by its first three vertices and the list consisting of its first vertex followed by its vertices from index $2$ onward. Natural subtraction truncates at zero, and the head lookup has default label $0$, although the branch using that head has length greater than $3$. No distinctness, nonemptiness or graph-validity condition is imposed on the input list. A case state is a face list and a Boolean flag called standard. A split rule carries arbitrary natural labels: node218 and node236 each have two children, edge and triangle each two, quad five, pent eleven, hex seven, and high, mid and addBig each one. At a quad$(a,b,c,d)$ branch, children $0,2$ split at $(b,c)$, children $1,3$ split at $(a,b)$, and child $4$ preserves the state. At pent$(a,b,c,d,e)$, form the cyclic dart list of those five labels and rotate it left once. Child $0$ preserves the state; children $1,\ldots,5$ split at respective entries $0,\ldots,4$; child $6+j$ for $0\leq j<5$ first splits at entry $j$ and then at entry $j$ of that dart list rotated left twice. At a hex rule, form its six-label dart list and rotate left once; child $0$ preserves the state and children $1,\ldots,6$ split at entries $0,\ldots,5$. Every such refinement sets standard to false, even if no containing face was found. Other rules preserve the entire state. Indexed dart reads use $(0,0)$ if out of range, though the specified child-index bounds put these lists' indices in range. A finite case tree has natural-number payloads at leaves and split rules with indexed child trees at branches. State annotation starts from any given state, replaces each leaf ordinal $k$ by the pair of $k$ and the current state, and recursively passes the child state just defined down every branch. It tests no branch guard, does not compare an ordinal with the size of a data table, and proves no geometric claim; the initial state is an argument, not required here to have a true standard flag.
--
--   **Source and scope.** Primary §9; formal_lp/hypermap/computations/informal_computations.hl:22–41 and main/prove_flyspeck_lp.hl:856–1037. Concatenates all 19,715 fixed graph records and preserves source face ordering and standard/refined state transitions.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §9; formal_lp/hypermap/computations/informal_computations.hl:22–41 and main/prove_flyspeck_lp.hl:856–1037. Concatenates all 19,715 fixed graph records and preserves source face ordering and standard/refined state transitions.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

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
import Definitions.Def_Kepler_LPCases
import Definitions.Def_Kepler_LPCaseData00
import Definitions.Def_Kepler_LPCaseData01
import Definitions.Def_Kepler_LPTemplateModel

set_option autoImplicit false
set_option maxRecDepth 4096

namespace KeplerMission.SourceLP



/-- Pinned final Flyspeck trees, in the unchanged tame archive order.
Revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Only branch and leaf specification data are included, no proof certificates. -/
def sourceGraphCodes : Array SourceGraphCode :=
  sourceCaseBlock0 ++ sourceCaseBlock1

end KeplerMission.SourceLP


set_option autoImplicit false

namespace KeplerMission.SourceLP

/-- Exact pure list refinement from `informal_computations.hl:22–41`.
No geometric property is asserted by this operation. -/
def splitFaceList : FaceList → ℕ × ℕ → FaceList
  | [], _ => []
  | f :: tail, d =>
      if d ∈ FaceList.faceDarts f then
        let i := (FaceList.faceDarts f).idxOf d
        let rotated := (f.rotate i).rotate (f.length - 1)
        if rotated.length ≤ 3 then rotated :: tail
        else rotated.take 3 :: ((rotated.headD 0) :: rotated.drop 2) :: tail
      else f :: splitFaceList tail d

/-- Refined fan state. The source branch tree determines both fields. -/
structure CaseState where
  faces : FaceList
  standard : Bool

def SplitRule.childState (rule : SplitRule) (i : Fin rule.arity)
    (state : CaseState) : CaseState :=
  let refine (d : ℕ × ℕ) := ⟨splitFaceList state.faces d, false⟩
  match rule with
  | .quad a b c _ =>
      if i.val = 0 ∨ i.val = 2 then refine (b, c)
      else if i.val = 1 ∨ i.val = 3 then refine (a, b)
      else state
  | .pent a b c d e =>
      let darts := (FaceList.faceDarts [a, b, c, d, e]).rotate 1
      if i.val = 0 then state
      else if i.val ≤ 5 then refine (darts[i.val - 1]?.getD (0, 0))
      else
        let first := splitFaceList state.faces (darts[i.val - 6]?.getD (0, 0))
        ⟨splitFaceList first ((darts.rotate 2)[i.val - 6]?.getD (0, 0)), false⟩
  | .hex a b c d e f =>
      let darts := (FaceList.faceDarts [a, b, c, d, e, f]).rotate 1
      if i.val = 0 then state else refine (darts[i.val - 1]?.getD (0, 0))
  | _ => state

structure LeafLocation where
  ordinal : ℕ
  state : CaseState

/-- Annotate every fixed source leaf by deterministic fan refinements. -/
def SourceCaseTree.withState (state : CaseState) : SourceCaseTree ℕ → SourceCaseTree LeafLocation
  | .leaf ordinal => .leaf ⟨ordinal, state⟩
  | .branch rule children => .branch rule (fun i =>
      (children i).withState (rule.childState i state))

end KeplerMission.SourceLP


