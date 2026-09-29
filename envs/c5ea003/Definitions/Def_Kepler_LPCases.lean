-- Prove2me | Definitions.Def_Kepler_LPCases
-- name    : Kepler_LPCases
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T02:58:29.427362+00:00
-- url     : https://prove2.me/theorems/4466afc3-8862-4148-bd3a-8143d91ad6ed
-- title:
--   Source case splits and tree decoding
-- statement:
--   A split rule is one of node218$(v)$, node236$(v)$, edge$(v,w)$, triangle$(v_0,v_1,v_2)$, quad$(v_0,v_1,v_2,v_3)$, pent$(v_0,\ldots,v_4)$, hex$(v_0,\ldots,v_5)$, high$(v)$, mid$(v,w)$ or addBig$(v_0,v_1,v_2)$, with arbitrary natural labels, including repetitions. Their numbers of children are respectively $2,2,2,2,5,11,7,1,1,1$. Given any functions $r:\mathbb N\to\mathbb R$ and $\ell:\mathbb N\times\mathbb N\to\mathbb R$, with no positivity, symmetry or geometric hypotheses, the following are the guards of the children in order, writing $r_v=r(v)$ and $l_{uv}=\ell(u,v)$. Rule 218 has children guarded by $109/50\leq r_v$ and $r_v\leq109/50$; rule 236 by $r_v\leq59/25$ and $59/25\leq r_v$; an edge rule by $9/4\leq l_{uv}$ and $l_{uv}\leq9/4$; a triangle rule by $l_{v_0v_1}+l_{v_1v_2}+l_{v_2v_0}$ being at least or at most $25/4$. For a quadrilateral set $a=l_{v_0v_2},b=l_{v_1v_3},t=\sqrt8$; its five guards are $a\leq b\land a\leq t$, $b\leq a\land b\leq t$, $a\leq b\land t\leq a\leq3$, $b\leq a\land t\leq b\leq3$, and $3\leq a\land3\leq b$. For a pentagon set $(a,b,c,d,e)=(l_{v_0v_2},l_{v_1v_3},l_{v_2v_4},l_{v_3v_0},l_{v_4v_1})$; its eleven guards are: all five at least $t$; $a\leq t\leq c,d$; $b\leq t\leq d,e$; $c\leq t\leq e,a$; $d\leq t\leq a,b$; $e\leq t\leq b,c$; $a,c\leq t$; $b,d\leq t$; $c,e\leq t$; $d,a\leq t$; and $e,b\leq t$. For a hexagon the six lengths are $l_{v_0v_2},l_{v_1v_3},l_{v_2v_4},l_{v_3v_5},l_{v_4v_0},l_{v_5v_1}$; its seven guards are all six at least $t$, followed by each individual length at most $t$. Rules high, mid and add_big each have one child with guard true.  The separately defined quadrilateral, pentagon and hexagon guard functions use precisely the same displayed inequalities for arbitrary real arguments $a,b,c,d,e,f,t$ as applicable; only their use in a split rule sets $t=\sqrt8$. Equalities can satisfy multiple children. For any type $\alpha$, with no finiteness or nonemptiness assumption, a finite case tree is either a leaf carrying an element of $\alpha$ or a branch carrying a split rule and exactly its prescribed indexed family of child trees. A tree reaches an element $a\in\alpha$ for given $r,\ell$ precisely when a finite path reaches a leaf with that value and each chosen child on the path satisfies its guard. This is existential path membership, not uniqueness of the path or of a leaf's payload. No theorem of guard coverage is asserted. The accepted textual branch tags are 218, 236 and high with one label; edge and mid with two; tri and add_big with three; quad with four; pent with five; and hex with six. Decoding a tag and label list requires exactly the indicated number of labels; any other combination fails. The recursive reader takes a natural fuel amount and a list of strings. Zero fuel always fails. Positive fuel reads a token l followed by a decimal natural-number token as a leaf ordinal, returning the remaining tokens; otherwise it reads a recognized branch tag, its prescribed number of natural-number label tokens, and then exactly its prescribed number of subtrees in child-index order. Each child is read at fuel one less than the parent's fuel; the unused token tail is threaded from child to child, while all siblings use that same reduced fuel. A missing token, unrecognized tag, failed natural-number parse, failed child or incorrect resulting child count makes the read fail. The top-level decoder splits a string at literal spaces, starts with fuel equal to the number of resulting tokens, and succeeds only if no tokens remain. Empty tokens arising from extra spaces are not removed. Leading zeroes in decimal numerals are allowed; labels and ordinals have no upper bound. These are definitions of syntax, guards, reachability and partial decoding, with no assertion that a particular string decodes or that any tree is geometrically realizable.
--
--   **Source and scope.** Primary §9; formal_lp/hypermap/main/prove_flyspeck_lp.hl:483–523,737–766,856–1037. Closed ordered-real branch conditions and deterministic decoding with all required children.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §9; formal_lp/hypermap/main/prove_flyspeck_lp.hl:483–523,737–766,856–1037. Closed ordered-real branch conditions and deterministic decoding with all required children.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

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
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

namespace KeplerMission.SourceLP

/-- Final Flyspeck split tags, with exactly their required vertex labels.
Source pin 1ce0353008eba83d3c76ae9a25c3c242e4802d53,
`formal_lp/hypermap/main/prove_flyspeck_lp.hl`, lines 483–523 and 737–1040.
The last three constructors record unary local-inequality derivations only. -/
inductive SplitRule where
  | node218 (v : ℕ)
  | node236 (v : ℕ)
  | edge (v w : ℕ)
  | triangle (v₀ v₁ v₂ : ℕ)
  | quad (v₀ v₁ v₂ v₃ : ℕ)
  | pent (v₀ v₁ v₂ v₃ v₄ : ℕ)
  | hex (v₀ v₁ v₂ v₃ v₄ v₅ : ℕ)
  | high (v : ℕ)
  | mid (v w : ℕ)
  | addBig (v₀ v₁ v₂ : ℕ)
  deriving DecidableEq, Repr

/-- Exact source child counts; in particular the hexagon split has seven children. -/
def SplitRule.arity : SplitRule → ℕ
  | .node218 _ | .node236 _ | .edge _ _ | .triangle _ _ _ => 2
  | .quad _ _ _ _ => 5
  | .pent _ _ _ _ _ => 11
  | .hex _ _ _ _ _ _ => 7
  | .high _ | .mid _ _ | .addBig _ _ _ => 1

/-- Five source quadrilateral alternatives, in source certificate order. -/
def quadGuards (a b t : ℝ) : Fin 5 → Prop :=
  ![a ≤ b ∧ a ≤ t, b ≤ a ∧ b ≤ t,
    a ≤ b ∧ t ≤ a ∧ a ≤ 3, b ≤ a ∧ t ≤ b ∧ b ≤ 3, 3 ≤ a ∧ 3 ≤ b]

/-- Eleven source pentagonal alternatives, in source certificate order. -/
def pentGuards (a b c d e t : ℝ) : Fin 11 → Prop :=
  ![t ≤ a ∧ t ≤ b ∧ t ≤ c ∧ t ≤ d ∧ t ≤ e,
    a ≤ t ∧ t ≤ c ∧ t ≤ d, b ≤ t ∧ t ≤ d ∧ t ≤ e,
    c ≤ t ∧ t ≤ e ∧ t ≤ a, d ≤ t ∧ t ≤ a ∧ t ≤ b,
    e ≤ t ∧ t ≤ b ∧ t ≤ c, a ≤ t ∧ c ≤ t, b ≤ t ∧ d ≤ t,
    c ≤ t ∧ e ≤ t, d ≤ t ∧ a ≤ t, e ≤ t ∧ b ≤ t]

/-- Seven source hexagonal alternatives, in source certificate order. -/
def hexGuards (a b c d e f t : ℝ) : Fin 7 → Prop :=
  ![t ≤ a ∧ t ≤ b ∧ t ≤ c ∧ t ≤ d ∧ t ≤ e ∧ t ≤ f,
    a ≤ t, b ≤ t, c ≤ t, d ≤ t, e ≤ t, f ≤ t]

/-- Restricted source branch semantics. The two real-valued arguments stand for
radii and pair distances; coverage holds for all such values. The source-specific
interface must bind them to norms and distances of its labeled placement.
Unary annotations impose no new condition and supply no theorem. -/
def SplitRule.Follows (radius : ℕ → ℝ) (length : ℕ → ℕ → ℝ)
    (rule : SplitRule) : Fin rule.arity → Prop :=
  match rule with
  | .node218 v => ![(109 : ℝ) / 50 ≤ radius v, radius v ≤ (109 : ℝ) / 50]
  | .node236 v => ![radius v ≤ (59 : ℝ) / 25, (59 : ℝ) / 25 ≤ radius v]
  | .edge v w => ![(9 : ℝ) / 4 ≤ length v w, length v w ≤ (9 : ℝ) / 4]
  | .triangle v₀ v₁ v₂ =>
      ![(25 : ℝ) / 4 ≤ length v₀ v₁ + length v₁ v₂ + length v₂ v₀,
        length v₀ v₁ + length v₁ v₂ + length v₂ v₀ ≤ (25 : ℝ) / 4]
  | .quad v₀ v₁ v₂ v₃ =>
      quadGuards (length v₀ v₂) (length v₁ v₃) (Real.sqrt 8)
  | .pent v₀ v₁ v₂ v₃ v₄ =>
      pentGuards (length v₀ v₂) (length v₁ v₃) (length v₂ v₄)
        (length v₃ v₀) (length v₄ v₁) (Real.sqrt 8)
  | .hex v₀ v₁ v₂ v₃ v₄ v₅ =>
      hexGuards (length v₀ v₂) (length v₁ v₃) (length v₂ v₄)
        (length v₃ v₅) (length v₄ v₀) (length v₅ v₁) (Real.sqrt 8)
  | .high _ | .mid _ _ | .addBig _ _ _ => ![True]

/-- Data-only source rule trees. The dependent child function forces every source
alternative to be present. The leaf payload has no role in coverage. -/
inductive SourceCaseTree (α : Type) where
  | leaf (data : α)
  | branch (rule : SplitRule) (children : Fin rule.arity → SourceCaseTree α)

/-- A path reaches a concrete leaf through the supported closed-order guards. -/
inductive SourceCaseTree.Reaches {α : Type} (radius : ℕ → ℝ) (length : ℕ → ℕ → ℝ) :
    SourceCaseTree α → α → Prop where
  | leaf (data : α) : Reaches radius length (.leaf data) data
  | branch (rule : SplitRule) (children : Fin rule.arity → SourceCaseTree α)
      (i : Fin rule.arity) (data : α)
      (hguard : rule.Follows radius length i)
      (hchild : Reaches radius length (children i) data) :
      Reaches radius length (.branch rule children) data

end KeplerMission.SourceLP


set_option autoImplicit false

namespace KeplerMission.SourceLP

/-- Number of source vertex labels consumed by a supported split tag. -/
def splitLabelCount : String → Option ℕ
  | "218" | "236" | "high" => some 1
  | "edge" | "mid" => some 2
  | "tri" | "add_big" => some 3
  | "quad" => some 4
  | "pent" => some 5
  | "hex" => some 6
  | _ => none

/-- Parsing is fail-closed: neither arbitrary predicates nor unknown tags are allowed. -/
def decodeSplit : String → List ℕ → Option SplitRule
  | "218", [v] => some (.node218 v)
  | "236", [v] => some (.node236 v)
  | "high", [v] => some (.high v)
  | "edge", [v, w] => some (.edge v w)
  | "mid", [v, w] => some (.mid v w)
  | "tri", [a, b, c] => some (.triangle a b c)
  | "add_big", [a, b, c] => some (.addBig a b c)
  | "quad", [a, b, c, d] => some (.quad a b c d)
  | "pent", [a, b, c, d, e] => some (.pent a b c d e)
  | "hex", [a, b, c, d, e, f] => some (.hex a b c d e f)
  | _, _ => none

/-- Prefix grammar: `l ordinal`, or a source tag, its labels, and every child.
Fuel bounds parser recursion only; insufficient fuel is an explicit failure. -/
def readCaseTree : ℕ → List String → Option (SourceCaseTree ℕ × List String)
  | 0, _ => none
  | fuel + 1, "l" :: ordinal :: rest => do
      return (.leaf (← ordinal.toNat?), rest)
  | fuel + 1, tag :: rest => do
      let count ← splitLabelCount tag
      let labels ← (rest.take count).mapM String.toNat?
      let rule ← decodeSplit tag labels
      let (children, remaining) ← (List.range rule.arity).foldlM
        (fun (acc : List (SourceCaseTree ℕ) × List String) _ => do
          let (child, tail) ← readCaseTree fuel acc.2
          return (acc.1 ++ [child], tail)) ([], rest.drop count)
      if h : children.length = rule.arity then
        return (.branch rule (fun i => children.get ⟨i.val, by simpa [h] using i.isLt⟩), remaining)
      else none
  | _ + 1, [] => none

def decodeCaseTree (code : String) : Option (SourceCaseTree ℕ) := do
  let tokens := code.splitOn " "
  let (tree, rest) ← readCaseTree tokens.length tokens
  if rest.isEmpty then some tree else none

end KeplerMission.SourceLP


