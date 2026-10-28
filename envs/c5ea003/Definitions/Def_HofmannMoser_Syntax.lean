-- Prove2me | Definitions.Def_HofmannMoser_Syntax
-- name    : HofmannMoser_Syntax
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-28T00:50:29.367838+00:00
-- url     : https://prove2.me/theorems/61209d66-e95d-417f-bb6f-d2f5f11a85bd
-- title:
--   Term-rewriting syntax, orthogonality, and counted evaluation
-- statement:
--   Foundational syntax and operational semantics for constructor term rewrite systems (Section 2, pp. 244–245).
--
--   Let $\mathcal{C}$ and $\mathcal{D}$ be arity-indexed families of constructor symbols and defined function symbols. First-order terms $t \in \mathcal{T}(\mathcal{C}, \mathcal{D}, \mathcal{V})$ (`Term C D`) are built from variables $x \in \mathbb{N}$, constructor applications $c(t_1, \dots, t_n)$, and defined applications $f(t_1, \dots, t_n)$. A ground constructor value (`IsValue`) is a term built solely from constructors.
--
--   A substitution $\sigma$ (`Substitution C D`) consists of a finite domain list $\operatorname{dom}(\sigma)$ and an assignment mapping variables to terms; it is normalised (`Substitution.Normalised`) when every $x \in \operatorname{dom}(\sigma)$ is mapped to a ground constructor value. A rewrite system $R$ (`RewriteSystem C D`) is a predicate on rewrite rules $f(l_1, \dots, l_n) \to r$ (`RewriteRule C D`), accompanied by standing predicates for finite signatures with at least one constant (`FiniteSignature C D`), finite rule sets (`FiniteSystem R`), left-linear non-overlapping constructor patterns (`SyntacticallyOrthogonal R`), and complete definedness on ground constructor arguments (`CompletelyDefined R`).
--
--   The big-step evaluation relation $\sigma \vdash t \Rightarrow^m v$ (`Evaluates R σ t m v`, Figure 1, p. 244) inductively counts the number $m \in \mathbb{N}$ of innermost rewrite steps needed to reduce $t\sigma$ to a ground constructor value $v$.
--
--   **Formalization Note** Variables are represented by natural numbers, arities are indexed by `Fin n`, and substitution domains are explicit finite lists so that restriction and domain membership remain constructive in core Lean 4 without Mathlib.
-- source:
--   Hofmann--Moser 2015, Multivariate Amortised Resource Analysis for Term Rewrite Systems, TLCA 2015, https://doi.org/10.4230/LIPIcs.TLCA.2015.241, Section 2, pp. 244--245, Figure 1

import Std

/-!
# The syntax and big-step semantics of Hofmann–Moser

Arity-correct first-order terms and Figure 1 of Martin Hofmann and Georg Moser,
*Multivariate Amortised Resource Analysis for Term Rewrite Systems*, TLCA 2015,
pp. 244–245, <https://doi.org/10.4230/LIPIcs.TLCA.2015.241>.

Countably many variables are represented by natural numbers; a substitution has a finite
list as its domain. Signature finiteness, orthogonality and complete definedness are global
conditions on the theorem's setting, rather than built into the evaluation relation.
-/

noncomputable section

namespace HofmannMoser

universe u

/-- First-order terms over constructor symbols `C` and defined symbols `D`, indexed by arity. -/
inductive Term (C D : Nat → Type u) : Type u
  | var : Nat → Term C D
  | func {n : Nat} : C n ⊕ D n → (Fin n → Term C D) → Term C D

namespace Term

variable {C D : Nat → Type u}

/-- The variables of a term, enumerated with multiplicity. -/
def variables : Term C D → List Nat
  | .var x => [x]
  | .func (n := n) _ args => (List.finRange n).flatMap fun i => variables (args i)

/-- Simultaneous substitution. -/
def subst (assignment : Nat → Term C D) : Term C D → Term C D
  | .var x => assignment x
  | .func f args => .func f fun i => subst assignment (args i)

/-- Capture-free variable renaming of a first-order term. -/
def rename (ρ : Nat → Nat) (t : Term C D) : Term C D := t.subst (fun x => .var (ρ x))

/-- The number of occurrences of a variable in a term. -/
def occurrences (x : Nat) (t : Term C D) : Nat := t.variables.count x

end Term

variable {C D : Nat → Type u}

/-- Constructor terms may contain variables and are used as rule patterns. -/
inductive IsConstructorTerm : Term C D → Prop
  | var (x : Nat) : IsConstructorTerm (.var x)
  | constructor {n : Nat} (c : C n) (args : Fin n → Term C D)
      (hargs : ∀ i, IsConstructorTerm (args i)) :
      IsConstructorTerm (.func (Sum.inl c) args)

/-- Values are the ground terms made exclusively from constructor symbols. -/
inductive IsValue : Term C D → Prop
  | constructor {n : Nat} (c : C n) (args : Fin n → Term C D)
      (hargs : ∀ i, IsValue (args i)) : IsValue (.func (Sum.inl c) args)

/-- A finite substitution; the assignment function outside its domain is immaterial. -/
structure Substitution (C D : Nat → Type u) where
  dom : List Nat
  assignment : Nat → Term C D

namespace Substitution

/-- The paper's normalisation condition for substitutions. -/
def Normalised (σ : Substitution C D) : Prop := ∀ x ∈ σ.dom, IsValue (σ.assignment x)

/-- Assignment on the domain and identity outside the domain. -/
def apply (σ : Substitution C D) (x : Nat) : Term C D :=
  if x ∈ σ.dom then σ.assignment x else .var x

/-- The capture-free simultaneous application of a substitution to a first-order term. -/
def instantiate (σ : Substitution C D) (t : Term C D) : Term C D := t.subst σ.apply

/-- Disjoint domains, as required by the paper's disjoint union notation. -/
def Disjoint (σ τ : Substitution C D) : Prop := ∀ x, x ∈ σ.dom → x ∉ τ.dom

/-- The union of two substitutions. Its intended use requires disjoint domains. -/
def union (σ τ : Substitution C D) : Substitution C D where
  dom := σ.dom ++ τ.dom
  assignment x := if x ∈ σ.dom then σ.assignment x else τ.assignment x

/-- The finite substitution that associates the distinct fresh variables with argument values. -/
def arguments {n : Nat} (xs : Fin n → Nat) (vs : Fin n → Term C D) : Substitution C D where
  dom := (List.finRange n).map xs
  assignment x := if h : ∃ i, xs i = x then vs (Classical.choose h) else .var x

end Substitution

/-- A rewrite rule headed by a defined symbol, prior to its pattern and variable conditions. -/
structure Rule (C D : Nat → Type u) where
  arity : Nat
  symbol : D arity
  patterns : Fin arity → Term C D
  rhs : Term C D

namespace Rule

/-- The full left-hand side of a rule, headed by its defined symbol. -/
def lhs (r : Rule C D) : Term C D := .func (Sum.inr r.symbol) r.patterns

/-- Variables of the left side, listed with multiplicity. -/
def lhsVariables (r : Rule C D) : List Nat :=
  (List.finRange r.arity).flatMap fun i => (r.patterns i).variables

/-- Constructor-pattern, no-extra-variable, and left-linearity conditions for one rule. -/
def IsLeftLinearConstructorRule (r : Rule C D) : Prop :=
  (∀ i, IsConstructorTerm (r.patterns i)) ∧
  (∀ x, x ∈ r.rhs.variables → x ∈ r.lhsVariables) ∧
  ∀ x, r.lhsVariables.count x ≤ 1

end Rule

/-- A term rewrite system; finiteness and orthogonality are separate conditions. -/
abbrev RewriteSystem (C D : Nat → Type u) := Rule C D → Prop

/--
The paper's finite signature has a nonempty constructor part and at least one constant in
the whole signature. The constant may be a constructor or a defined symbol (p. 244).
-/
def FiniteSignature (C D : Nat → Type u) : Prop :=
  (∃ cs : List (Σ n, C n), ∀ c, c ∈ cs) ∧
  (∃ ds : List (Σ n, D n), ∀ d, d ∈ ds) ∧
  (∃ n, Nonempty (C n)) ∧
  (Nonempty (C 0) ∨ Nonempty (D 0))

/-- The paper's assumption that a rewrite system consists of finitely many rules. -/
def FiniteSystem (R : RewriteSystem C D) : Prop :=
  ∃ rules : List (Rule C D), ∀ r, R r ↔ r ∈ rules

/-- Every rule has constructor patterns, no extra right-side variables, and a linear left side. -/
def LeftLinearConstructorSystem (R : RewriteSystem C D) : Prop :=
  ∀ r, R r → r.IsLeftLinearConstructorRule

/-- Rules are identified up to a bijective, consistent renaming of all their variables. -/
def Rule.AlphaEquivalent (r₁ r₂ : Rule C D) : Prop :=
  ∃ ρ : Nat → Nat, Function.Injective ρ ∧ Function.Surjective ρ ∧
    r₁.lhs.rename ρ = r₂.lhs ∧ r₁.rhs.rename ρ = r₂.rhs

/--
Root unifiability after standardising two rules apart. For constructor systems every proper
non-variable subterm of a left-hand side is constructor-headed; hence an overlap with a
defined-headed rule can occur only at the root. Here the unifier is an arbitrary finite
term substitution, not necessarily a value substitution.
-/
def Rule.RootOverlap (r₁ r₂ : Rule C D) : Prop :=
  ∃ (ρ₁ ρ₂ : Nat → Nat) (σ : Substitution C D),
    Function.Injective ρ₁ ∧ Function.Injective ρ₂ ∧
    (∀ x, x ∈ r₁.lhsVariables → ∀ y, y ∈ r₂.lhsVariables → ρ₁ x ≠ ρ₂ y) ∧
    σ.instantiate (r₁.lhs.rename ρ₁) = σ.instantiate (r₂.lhs.rename ρ₂)

/--
Left-linearity and absence of root overlaps between rules distinct up to renaming. This is
the explicit constructor-system reading of the paper's orthogonality assumption. Its
equivalence with a chosen external critical-pair convention remains to be independently
checked before the overall mission statement is treated as audited.
-/
def SyntacticallyOrthogonal (R : RewriteSystem C D) : Prop :=
  LeftLinearConstructorSystem R ∧
  ∀ r₁ r₂, R r₁ → R r₂ → ¬ r₁.AlphaEquivalent r₂ → ¬ r₁.RootOverlap r₂

/-- A one-hole term context, used to define contextual rewrite steps. -/
inductive Context (C D : Nat → Type u) : Type u
  | hole : Context C D
  | node {n : Nat} : C n ⊕ D n → (Fin n → Term C D) → Fin n → Context C D → Context C D

namespace Context

/-- Insert a term into the unique hole of a context. -/
def plug : Context C D → Term C D → Term C D
  | .hole, t => t
  | .node f args j inner, t =>
      .func f (fun i => if i = j then inner.plug t else args i)

end Context

/-- A standard contextual rewrite step, allowing an injectively renamed instance of a rule. -/
def RewriteStep (R : RewriteSystem C D) (t s : Term C D) : Prop :=
  ∃ (r : Rule C D) (ρ : Nat → Nat) (σ : Substitution C D) (ctx : Context C D),
    R r ∧ Function.Injective ρ ∧
    t = ctx.plug (σ.instantiate (r.lhs.rename ρ)) ∧
    s = ctx.plug (σ.instantiate (r.rhs.rename ρ))

/-- A term is in normal form if no contextual rewrite step starts there. -/
def NormalForm (R : RewriteSystem C D) (t : Term C D) : Prop :=
  ∀ s, ¬ RewriteStep R t s

/-- Complete definedness: every ground normal form is a constructor value (p. 244). -/
def CompletelyDefined (R : RewriteSystem C D) : Prop :=
  ∀ t, t.variables = [] → NormalForm R t → IsValue t

/--
The resource-counted big-step evaluation of Figure 1. In composition, an injective fresh
family of temporary variables names the argument values. The counted rewrite rule uses a
normalised matching substitution disjoint from the current one; each rewrite costs one.
Before matching, an injective variable renaming is applied to both sides of the selected
rule. This makes explicit the standard convention of freshening rewrite-rule variables,
which is necessary when the current substitution already uses a rule's variable names.
-/
inductive Evaluates (R : RewriteSystem C D) : Substitution C D → Term C D → Nat → Term C D → Prop
  | var (σ : Substitution C D) (x : Nat) (v : Term C D)
      (hx : x ∈ σ.dom) (hv : σ.assignment x = v) :
      Evaluates R σ (.var x) 0 v
  | constructor {n : Nat} (σ : Substitution C D) (c : C n) (xs : Fin n → Nat)
      (vs : Fin n → Term C D) (hx : ∀ i, xs i ∈ σ.dom)
      (hv : ∀ i, σ.assignment (xs i) = vs i) :
      Evaluates R σ (.func (Sum.inl c) fun i => .var (xs i)) 0
        (.func (Sum.inl c) vs)
  | rewrite {n : Nat} (σ τ : Substitution C D) (f : D n) (xs : Fin n → Nat)
      (r : Rule C D) (hr : R r) (ha : r.arity = n) (hf : ha ▸ r.symbol = f)
      (ρ : Nat → Nat) (hrenaming : Function.Injective ρ)
      (hmatch : ∀ i, xs i ∈ σ.dom ∧
        σ.assignment (xs i) = τ.instantiate ((r.patterns (Fin.cast ha.symm i)).rename ρ))
      (hdisjoint : σ.Disjoint τ) (hnorm : τ.Normalised) (m : Nat) (v : Term C D)
      (heval : Evaluates R (σ.union τ) (r.rhs.rename ρ) m v) :
      Evaluates R σ (.func (Sum.inr f) fun i => .var (xs i)) (m + 1) v
  | composition {n : Nat} (σ : Substitution C D) (f : C n ⊕ D n)
      (ts : Fin n → Term C D) (xs : Fin n → Nat) (vs : Fin n → Term C D)
      (costs : Fin n → Nat) (outerCost : Nat) (v : Term C D)
      (hinj : Function.Injective xs) (hfresh : ∀ i, xs i ∉ σ.dom)
      (hfreshTerm : ∀ i j, xs i ∉ (ts j).variables)
      (hargs : ∀ i, Evaluates R σ (ts i) (costs i) (vs i))
      (houter : Evaluates R (σ.union (Substitution.arguments xs vs))
        (.func f fun i => .var (xs i)) outerCost v) :
      Evaluates R σ (.func f ts) (outerCost + ((List.finRange n).map costs).sum) v

end HofmannMoser


