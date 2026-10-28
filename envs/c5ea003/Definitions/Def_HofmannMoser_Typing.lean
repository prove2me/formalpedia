-- Prove2me | Definitions.Def_HofmannMoser_Typing
-- name    : HofmannMoser_Typing
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-28T00:51:00.87127+00:00
-- url     : https://prove2.me/theorems/65bbf742-e2df-4220-86e9-e847a4e85f55
-- title:
--   Resource typing rules and bounded term rewrite systems
-- statement:
--   Resource-annotated signatures, the amortised resource typing judgment, and syntactic boundedness of term rewrite systems (Section 4, pp. 249–252).
--
--   An annotated signature (`AnnotatedSignature C D`, Definition 14, p. 249) assigns a relation between length-$n$ input annotations $Q$ and length-$1$ output annotations $Q'$ to each $n$-ary defined symbol $f \in \mathcal{D}_n$. The structure `AnnotatedSignatures C D` bundles separate signature relations for charged (`TypingMode.counted`, $\vdash$) and uncharged (`TypingMode.costFree`, $\vdash^{\mathrm{cf}}$) derivations, and `AnnotatedSignatureExtensional` expresses invariance under coefficient-wise annotation equality (`annotationEq`, defined via `annotationCoefficient`).
--
--   The inductive judgment $\Gamma : Q \vdash^{(\mathrm{cf})} t : Q'$ (`Typing S P F mode n xs Q t Q'`, Figure 2, p. 251) formalizes all eight typing rules of the paper:
--   1. `variable`: typing a single variable $x : Q \vdash^{(\mathrm{cf})} x : Q$.
--   2. `defined`: typing a flat defined call $f(x_1, \dots, x_n)$ from $(Q, Q') \in F(\text{mode})(f)$.
--   3. `constructor`: typing a flat constructor application $c(x_1, \dots, x_n)$ with input annotation $\triangleleft_c(Q)$ and output annotation $Q$.
--   4. `weakenAnnotations`: relaxing input and output annotations along pointwise coefficient inequality $P_0 \le Q$ and $Q' \le P'$ (`annotationLe`).
--   5. `exchange`: simultaneously permuting context variables and annotation coordinates along a bijection $\rho : \operatorname{Fin}(n) \to \operatorname{Fin}(n)$ (`annotationReindex`).
--   6. `weakenContext`: dropping a trailing context variable by projecting the annotation at the canonical basic function $\emptyset$ (`annotationProject`).
--   7. `share`: contracting two distinct variables $x, y$ into a fresh variable $z$ via $\Upsilon(Q)$ (`annotationShare`).
--   8. `composition`: typing an application $f(t_0, \dots, t_{\text{last}})$ of positive arity $\text{last} + 1$ across concatenated argument contexts (`argumentContexts`), governed by the coupling equations `compositionCoefficients` and the mode selector `listPremiseMode` (which uses counted mode for the all-canonical index $\vec{\jmath}_i = \vec{\emptyset}$ inside a counted parent derivation and cost-free mode otherwise).
--
--   Finally, `PatternExpansion` and `additiveShiftAt` formalize iterated constructor pattern unfolding across rule left-hand sides, and `Bounded` / `BoundedSignatures` (Definition 15, p. 250) state that every rewrite rule $f(l_1, \dots, l_n) \to r$ in $R$ and every signature annotation $(Q, Q')$ for $f$ expands to pattern variables $(x_1, \dots, x_l)$ and an annotation $P_0$ typing $r : Q'$ with $P_0 + 1 = \text{shifted}$ in counted mode and $P_0 = \text{shifted}$ in cost-free mode.
-- source:
--   Hofmann--Moser 2015, Multivariate Amortised Resource Analysis for Term Rewrite Systems, TLCA 2015, https://doi.org/10.4230/LIPIcs.TLCA.2015.241, Section 4, pp. 249--252, Definitions 14--15, Figure 2

import Definitions.Def_HofmannMoser_Syntax
import Definitions.Def_HofmannMoser_Potential

/-!
# Resource typing and bounded term rewrite systems for Hofmann–Moser

Definitions for Section 4 (Definitions 14 and 15, Figure 2) of Martin Hofmann and Georg Moser,
*Multivariate Amortised Resource Analysis for Term Rewrite Systems*, TLCA 2015, pp. 249–252,
<https://doi.org/10.4230/LIPIcs.TLCA.2015.241>.

Annotations are indexed by tuples of basic resource functions (`BasicFunction C`) with respect
to a fixed representative policy (`RepPolicy C`). The typing judgment `Typing` encodes the
inference rules of Figure 2 with counted and cost-free modes (`TypingMode`), separate
counted and cost-free annotated signatures (`AnnotatedSignatures`), simultaneous context
and annotation coordinate exchange, context weakening, annotation weakening (including the
empty context), sharing (`annotationShare`), and `n`-ary composition (`compositionCoefficients`).
`Bounded` and `BoundedSignatures` encode Definition 15 via concrete left-hand-side constructor
pattern expansion (`PatternExpansion`).
-/

namespace HofmannMoser

universe u

/-- Definition 14: an annotated signature assigns a collection of input/output annotation
pairs `(Q, Q')` to each `n`-ary defined function symbol `f ∈ D n`, where `Q` has length `n`
and `Q'` has length `1`. -/
abbrev AnnotatedSignature (C D : Nat → Type u) :=
  (n : Nat) → D n → Annotation C n → Annotation C 1 → Prop

/-- The two judgment modes occurring in Figure 2 (p. 251): charged (`counted`, `⊢`) and
uncharged (`costFree`, `⊢^{cf}`). -/
inductive TypingMode where
  | counted
  | costFree
  deriving DecidableEq

/-- Separate annotated signatures for charged (`counted`) and uncharged (`costFree`)
judgments (cf. p. 250 and the multiplication example on p. 252). -/
structure AnnotatedSignatures (C D : Nat → Type u) where
  counted : AnnotatedSignature C D
  costFree : AnnotatedSignature C D

/-- Select the annotated signature corresponding to a judgment mode. -/
def AnnotatedSignatures.get {C D : Nat → Type u} (F : AnnotatedSignatures C D) :
    TypingMode → AnnotatedSignature C D
  | .counted => F.counted
  | .costFree => F.costFree

/-- Reindex the coordinates of an annotation along `ρ`. When used in the exchange rule,
the same bijection reindexes both the context variables and every basic-function tuple. -/
def annotationReindex {C : Nat → Type u} {n : Nat} (ρ : Fin n → Fin n)
    (Q : Annotation C n) : Annotation C n :=
  Q.map fun entry ↦ (fun i ↦ entry.1 (ρ i), entry.2)

/-- The coefficient `q_{(p₁, …, p_n)}` of a basic-function tuple `index` in an annotation `Q`,
obtained by summing the weights of all entries in `Q` with key `index`. -/
noncomputable def annotationCoefficient {C : Nat → Type u} {n : Nat}
    (Q : Annotation C n) (index : Fin n → BasicFunction C) : Rat := by
  classical
  exact (Q.map fun entry ↦ if entry.1 = index then entry.2.1 else 0).sum

/-- Equality of annotations as finitely supported coefficient families over basic-function
tuples. -/
def annotationEq {C : Nat → Type u} {n : Nat} (P Q : Annotation C n) : Prop :=
  ∀ index, annotationCoefficient P index = annotationCoefficient Q index

/-- Pointwise comparison `P ≤ Q` of annotation coefficient families (§3, p. 249). -/
def annotationLe {C : Nat → Type u} {n : Nat} (P Q : Annotation C n) : Prop :=
  ∀ index, annotationCoefficient P index ≤ annotationCoefficient Q index

/-- An annotated signature on list representations is extensional when membership depends
only on the represented coefficient families (`annotationEq`). -/
def AnnotatedSignatureExtensional {C D : Nat → Type u} (F : AnnotatedSignature C D) : Prop :=
  ∀ n (f : D n) (P P' : Annotation C n) (Q Q' : Annotation C 1),
    annotationEq P P' → annotationEq Q Q' → (F n f P Q ↔ F n f P' Q')

/-- Read the coefficient of a basic-function tuple given as a list `indices` of length `n`.
Lists of length different from `n` return `0` and lie outside the length-guarded equations
of `compositionCoefficients`. -/
noncomputable def annotationCoefficientList {C : Nat → Type u} {n : Nat}
    (Q : Annotation C n) (indices : List (BasicFunction C)) : Rat := by
  classical
  exact if h : indices.length = n then
    annotationCoefficient Q (fun i ↦ indices.get ⟨i.val, by simp [h, i.isLt]⟩)
  else 0

/-- Total number of context variables across argument blocks in `[start, stop)`. -/
def contextWidth (lengths : Nat → Nat) (start stop : Nat) : Nat :=
  (((List.range (stop - start)).map fun k ↦ lengths (start + k))).sum

/-- The coefficient equations of the `n`-ary composition rule in Figure 2 (p. 251; see also
p. 250 and (8) on p. 253), for a positive number `last + 1` of arguments. For each argument
position `i`, `P i j` and `R i j` are the input and output annotations indexed by the list `j`
of `i` preceding output basic functions and `contextWidth lengths (i + 1) (last + 1)` following
context basic functions. -/
def compositionCoefficients {C : Nat → Type u} (last : Nat) (lengths : Nat → Nat)
    (Q : Annotation C (contextWidth lengths 0 (last + 1)))
    (S : Annotation C (last + 1))
    (P : (i : Nat) → List (BasicFunction C) → Annotation C (lengths i))
    (R : Nat → List (BasicFunction C) → Annotation C 1) : Prop :=
  (∀ first rest, first.length = lengths 0 →
    rest.length = contextWidth lengths 1 (last + 1) →
    annotationCoefficientList Q (first ++ rest) = annotationCoefficientList (P 0 rest) first) ∧
  (∀ i, i < last → ∀ before nextContext after output,
    before.length = i → nextContext.length = lengths (i + 1) →
    after.length = contextWidth lengths (i + 2) (last + 1) →
    annotationCoefficientList (P (i + 1) (before ++ [output] ++ after)) nextContext =
      annotationCoefficientList (R i (before ++ nextContext ++ after)) [output]) ∧
  (∀ before output, before.length = last →
    annotationCoefficientList S (before ++ [output]) =
      annotationCoefficientList (R last before) [output])

/-- Replace position `i` of a list `xs` by the list `children`, preserving the order of all
other entries. -/
def replaceAt {α : Type u} (xs : List α) (i : Nat) (children : List α) : List α :=
  xs.take i ++ children ++ xs.drop (i + 1)

/-- Replacing a valid index `i < xs.length` changes the list length by `children.length - 1`. -/
theorem replaceAt_length {α : Type u} (xs : List α) (i : Nat) (children : List α)
    (hi : i < xs.length) : (replaceAt xs i children).length = xs.length - 1 + children.length := by
  simp only [replaceAt, List.length_append, List.length_take, List.length_drop]
  simp only [Nat.min_eq_left (Nat.le_of_lt hi)]
  omega

/-- Expand the basic function at coordinate `pos` of an annotation `Q` at constructor `c`
using the transitions of its fixed representative `P.rep (entry.1 pos)`, replacing that
coordinate in place by the `k` rerooted child basic functions. -/
def additiveShiftAt {C : Nat → Type u} {n k : Nat}
    (P : RepPolicy C) (pos : Fin n) (c : C k) (Q : Annotation C n) :
    Annotation C (n - 1 + k) :=
  Q.flatMap fun entry ↦
    let A := P.rep (entry.1 pos)
    ((A.rules k c).filter fun tr ↦ tr.2 == A.final).map fun tr ↦
      let old := List.ofFn entry.1
      let children := List.ofFn fun i ↦ BasicFunction.reroot A (tr.1 i)
      let new := replaceAt old pos.val children
      have hlen : new.length = n - 1 + k := by
        rw [replaceAt_length old pos.val children (by simp [old, pos.isLt])]
        simp [old, children]
      (fun i ↦ new.get ⟨i.val, by simp [hlen, i.isLt]⟩, entry.2)

/-- Expanding a constructor pattern at `pos` changes the pattern list length by `k - 1`. -/
theorem replacePattern_length {C D : Nat → Type u} (patterns : List (Term C D))
    (pos : Fin patterns.length) {k : Nat} (args : Fin k → Term C D) :
    (replaceAt patterns pos.val (List.ofFn args)).length = patterns.length - 1 + k := by
  rw [replaceAt_length patterns pos.val (List.ofFn args) pos.isLt]
  simp

/-- Iterated constructor shift across a list of rule patterns (Definition 15, p. 250).
Each step expands a constructor subterm `c(t₁, …, t_k)` at coordinate `pos` and applies
`additiveShiftAt P pos c` at the same coordinate of the annotation, terminating when all
remaining pattern positions are variables `variables.map Term.var`. -/
inductive PatternExpansion {C D : Nat → Type u} (P : RepPolicy C) :
    (patterns : List (Term C D)) → Annotation C patterns.length →
      (variables : List Nat) → Annotation C variables.length → Prop
  | done (variables : List Nat) (Q : Annotation C variables.length) :
      PatternExpansion P (variables.map Term.var)
        ((List.length_map Term.var).symm ▸ Q) variables Q
  | step {k : Nat} (patterns : List (Term C D)) (pos : Fin patterns.length)
      (c : C k) (args : Fin k → Term C D) (hPattern : patterns.get pos = .func (.inl c) args)
      (Q : Annotation C patterns.length) (variables : List Nat)
      (Q' : Annotation C variables.length)
      (hNext : PatternExpansion P (replaceAt patterns pos.val (List.ofFn args))
        ((replacePattern_length patterns pos args).symm ▸ additiveShiftAt P pos c Q)
        variables Q') :
      PatternExpansion P patterns Q variables Q'

/-- Concatenate the argument contexts `Γ₁, …, Γ_{arity}` in order. -/
def argumentContexts (contexts : Nat → List Nat) (arity : Nat) : List Nat :=
  (List.range arity).flatMap contexts

/-- Total length of the concatenated argument contexts. -/
theorem argumentContexts_length (contexts : Nat → List Nat) (arity : Nat) :
    (argumentContexts contexts arity).length =
      contextWidth (fun i ↦ (contexts i).length) 0 arity := by
  simp [argumentContexts, contextWidth, List.length_flatMap]

/-- Figure 2's `⊢^{(cf)}` mode-selection convention (p. 251): inside a counted composition,
the all-canonical index `j⃗_i = ∅⃗` uses a counted premise (`counted`), and every other index
`j⃗_i ≠ ∅⃗` uses a cost-free premise (`costFree`). Inside a cost-free composition, all argument
premises are cost-free. -/
noncomputable def listPremiseMode {C : Nat → Type u} (S : FiniteConstructors C)
    (parent : TypingMode) (indices : List (BasicFunction C)) : TypingMode := by
  classical
  exact if parent = .costFree then .costFree
    else if ∀ p ∈ indices, p = BasicFunction.canonical S
      then .counted else .costFree

/-- The resource-analysis typing judgment `Γ : Q ⊢^{(cf)} t : Q'` of Figure 2 (p. 251),
parameterized by the finite constructor signature `S`, the representative policy `P`, and the
counted/cost-free annotated signatures `F`. -/
inductive Typing {C D : Nat → Type u} (S : FiniteConstructors C)
    (P : RepPolicy C) (F : AnnotatedSignatures C D) :
    TypingMode → (n : Nat) → (Fin n → Nat) → Annotation C n → Term C D →
      Annotation C 1 → Prop
  | variable (mode : TypingMode) (x : Nat) (Q : Annotation C 1) :
      Typing S P F mode 1 (fun _ ↦ x) Q (.var x) Q
  | defined (mode : TypingMode) {n : Nat} (f : D n) (xs : Fin n → Nat)
      (Q : Annotation C n) (Q' : Annotation C 1) (hDistinct : Function.Injective xs)
      (hannotated : F.get mode n f Q Q') :
      Typing S P F mode n xs Q (.func (.inr f) (fun i ↦ .var (xs i))) Q'
  | constructor (mode : TypingMode) {n : Nat} (c : C n) (xs : Fin n → Nat)
      (Q : Annotation C 1) (hDistinct : Function.Injective xs) :
      Typing S P F mode n xs (Nat.zero_add n ▸ additiveShift P (m := 0) c Q)
        (.func (.inl c) (fun i ↦ .var (xs i))) Q
  | weakenAnnotations (mode : TypingMode) {n : Nat} (xs : Fin n → Nat)
      (P₀ Q : Annotation C n) (P' Q' : Annotation C 1) (t : Term C D)
      (hDistinct : Function.Injective xs)
      (h : Typing S P F mode n xs P₀ t P') (hInput : annotationLe P₀ Q)
      (hOutput : annotationLe Q' P') : Typing S P F mode n xs Q t Q'
  | exchange (mode : TypingMode) {n : Nat} (xs : Fin n → Nat) (ρ : Fin n → Fin n)
      (hInjective : Function.Injective ρ) (hSurjective : Function.Surjective ρ)
      (Q : Annotation C n) (Q' : Annotation C 1) (t : Term C D)
      (h : Typing S P F mode n xs Q t Q') :
      Typing S P F mode n (fun i ↦ xs (ρ i)) (annotationReindex ρ Q) t Q'
  | weakenContext (mode : TypingMode) {n : Nat} (xs : Fin (n + 1) → Nat)
      (Q : Annotation C (n + 1)) (Q' : Annotation C 1) (t : Term C D)
      (hDistinct : Function.Injective xs)
      (h : Typing S P F mode n (fun i ↦ xs (Fin.castSucc i))
        (annotationProject Q (canonicalTuple S 1)) t Q') :
      Typing S P F mode (n + 1) xs Q t Q'
  | share (mode : TypingMode) {n : Nat} (xs : Fin n → Nat) (x y z : Nat)
      (Q : Annotation C (n + 2)) (Q' : Annotation C 1) (t : Term C D)
      (hContext : Function.Injective xs) (hDistinct : x ≠ y)
      (hFresh : ∀ i, xs i ≠ x ∧ xs i ≠ y ∧ xs i ≠ z)
      (hNew : z ≠ x ∧ z ≠ y ∧ z ∉ t.variables)
      (h : Typing S P F mode (n + 2)
        (Fin.addCases xs (fun i ↦ if i.val = 0 then x else y)) Q t Q') :
      Typing S P F mode (n + 1) (Fin.addCases xs (fun _ ↦ z))
        (annotationShare S P Q) (t.rename fun v ↦ if v = x ∨ v = y then z else v) Q'
  | composition (mode : TypingMode) (last : Nat) (f : C (last + 1) ⊕ D (last + 1))
      (contexts : Nat → List Nat) (terms : Nat → Term C D) (fresh : Fin (last + 1) → Nat)
      (Q : Annotation C (argumentContexts contexts (last + 1)).length)
      (S' : Annotation C (last + 1)) (Q' : Annotation C 1)
      (P_arg : (i : Nat) → List (BasicFunction C) → Annotation C (contexts i).length)
      (R_arg : Nat → List (BasicFunction C) → Annotation C 1)
      (hContexts : (argumentContexts contexts (last + 1)).Nodup)
      (hCoverage : ∀ i, i < last + 1 → ∀ x, x ∈ (terms i).variables → x ∈ contexts i)
      (hDistinct : Function.Injective fresh)
      (hFresh : ∀ i, fresh i ∉ argumentContexts contexts (last + 1) ∧
        ∀ j, j < last + 1 → fresh i ∉ (terms j).variables)
      (hCoefficients : compositionCoefficients last (fun i ↦ (contexts i).length)
        (argumentContexts_length contexts (last + 1) ▸ Q) S' P_arg R_arg)
      (hArguments : ∀ i, i < last + 1 → ∀ indices,
        indices.length = i + contextWidth (fun k ↦ (contexts k).length) (i + 1) (last + 1) →
        Typing S P F (listPremiseMode S mode indices) (contexts i).length
          (contexts i).get (P_arg i indices) (terms i) (R_arg i indices))
      (hFunction : Typing S P F mode (last + 1) fresh S'
        (.func f (fun i ↦ .var (fresh i))) Q') :
      Typing S P F mode (argumentContexts contexts (last + 1)).length
        (argumentContexts contexts (last + 1)).get Q
        (.func f (fun i ↦ terms i.val)) Q'

/-- One unit of rational potential. -/
def onePotential : {q : Rat // 0 ≤ q} := ⟨1, by decide⟩

/-- Definition 15 (p. 250): a TRS `R` is bounded (`mode = .counted`) or weakly bounded
(`mode = .costFree`) with respect to `F` if for every rule `f(l₁, …, l_n) → r` in `R` and
every annotation pair `(Q, Q')` in `F.get mode` for `f`, iteratively shifting `Q` across the
constructors of `l₁, …, l_n` yields an annotation `shifted` on the pattern variables
`variables = [x₁, …, x_l]` and an annotation `P₀` with `P₀ + 1 = shifted` (when `counted`)
or `P₀ = shifted` (when `costFree`) such that `x₁, …, x_l : P₀ ⊢^{(cf)} r : Q'` is derivable. -/
def Bounded {C D : Nat → Type u} (S : FiniteConstructors C) (P : RepPolicy C)
    (F : AnnotatedSignatures C D) (R : RewriteSystem C D) (mode : TypingMode) : Prop :=
  ∀ rule, R rule → ∀ (Q : Annotation C rule.arity) (Q' : Annotation C 1),
    F.get mode rule.arity rule.symbol Q Q' →
    ∃ (variables : List Nat) (P₀ shifted : Annotation C variables.length),
      PatternExpansion P (List.ofFn rule.patterns) ((List.length_ofFn).symm ▸ Q)
        variables shifted ∧
      (match mode with
       | .counted => annotationEq (addConstant S P₀ onePotential) shifted
       | .costFree => annotationEq P₀ shifted) ∧
      Typing S P F mode variables.length variables.get P₀ rule.rhs Q'

/-- Both boundedness obligations required when counted derivations invoke cost-free premises:
`R` is bounded with respect to `F.counted` and weakly bounded with respect to `F.costFree`. -/
def BoundedSignatures {C D : Nat → Type u} (S : FiniteConstructors C) (P : RepPolicy C)
    (F : AnnotatedSignatures C D) (R : RewriteSystem C D) : Prop :=
  Bounded S P F R .counted ∧ Bounded S P F R .costFree

end HofmannMoser


