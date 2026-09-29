-- Prove2me | Definitions.Def_Evergreen_Factor_Basic_2
-- name    : Evergreen_Factor_Basic_2
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:36:49.480011+00:00
-- url     : https://prove2.me/theorems/81999976-cec8-40de-94da-f48c9f15f68c
-- title:
--   Aether Catalog definitions — Evergreen_Factor_Basic_2
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.Factor.Basic.2`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/Factor/Basic_2.lean by skeleton subtraction
import Mathlib

/-!
# The Algebra of Adversarial Attacks

A formal framework connecting adversarial attacks on classifiers to oracle theory
and Boolean algebra. We formalize:

1. **Classifiers** as functions from feature spaces to label sets
2. **Adversarial attacks** as perturbation functions on the feature space
3. **Attack composition** forming a monoid (and group for invertible attacks)
4. **Robustness** as invariance of classification under perturbations
5. **The Contrarian Attack Theorem** — connection to anti-oracles
6. **Attack lattice** — Boolean algebra structure on attack sets
7. **Robustness regions** as downward-closed sets in the attack lattice

## Key Results

- `attack_comp_assoc`: Attack composition is associative
- `contrarian_attack_theorem`: A classifier attacked by complement-flip ≡ anti-oracle
- `robust_monotone`: Robustness is monotone w.r.t. attack budget inclusion
- `attack_robust_complement`: Attacked set and robust set partition the space
- `attack_as_pullback`: Adversarial attack = oracle pullback
-/

noncomputable section
open Set Function Classical

/-! ## Section 1: Classifiers and Decision Regions -/

/-- A Classifier maps feature vectors to labels. -/
structure Classifier (X : Type*) (L : Type*) where
  classify : X → L

/-- The decision region for label l: the set of inputs classified as l. -/
def Classifier.decisionRegion {X L : Type*} (c : Classifier X L) (l : L) : Set X :=
  {x | c.classify x = l}



/-! ## Section 2: Adversarial Attacks -/

/-- An AdversarialAttack is a perturbation function on the input space. -/
@[ext]
structure AdversarialAttack (X : Type*) where
  perturb : X → X

namespace AdversarialAttack

variable {X L : Type*}

/-- The identity attack: does nothing. -/
def idAttack : AdversarialAttack X where
  perturb := _root_.id

/-- Compose two attacks: apply a₁ first, then a₂. -/
def comp (a₂ a₁ : AdversarialAttack X) : AdversarialAttack X where
  perturb := a₂.perturb ∘ a₁.perturb

/-- Attack composition is associative. -/
theorem comp_assoc (a₃ a₂ a₁ : AdversarialAttack X) :
    (a₃.comp a₂).comp a₁ = a₃.comp (a₂.comp a₁) := by
  ext x; simp [comp, Function.comp]

/-- Identity is a left identity for composition. -/
theorem idAttack_comp (a : AdversarialAttack X) : idAttack.comp a = a := by
  ext x; simp [comp, idAttack]

/-- Identity is a right identity for composition. -/
theorem comp_idAttack (a : AdversarialAttack X) : a.comp idAttack = a := by
  ext x; simp [comp, idAttack]

/-- Attacks form a monoid under composition. -/
instance : Monoid (AdversarialAttack X) where
  mul := comp
  one := idAttack
  mul_assoc := comp_assoc
  one_mul := idAttack_comp
  mul_one := comp_idAttack

/-- The attack applied to a classifier yields a new classifier. -/
def applyToClassifier (a : AdversarialAttack X) (c : Classifier X L) :
    Classifier X L where
  classify := c.classify ∘ a.perturb

/-- Attack success: the attack causes misclassification on input x. -/
def succeeds (a : AdversarialAttack X) (c : Classifier X L) (x : X) : Prop :=
  c.classify (a.perturb x) ≠ c.classify x

/-- The attacked set: all inputs where the attack changes the classification. -/
def attackedSet (a : AdversarialAttack X) (c : Classifier X L) : Set X :=
  {x | a.succeeds c x}



end AdversarialAttack

/-! ## Section 3: Robustness -/

/-- A classifier is robust to an attack at point x. -/
def robust_at {X L : Type*} (c : Classifier X L) (a : AdversarialAttack X) (x : X) : Prop :=
  c.classify (a.perturb x) = c.classify x

/-- A classifier is robust to a set of attacks. -/
def robust {X L : Type*} (c : Classifier X L) (S : Set (AdversarialAttack X)) : Prop :=
  ∀ a ∈ S, ∀ x, robust_at c a x

/-- The robustness region: all attacks a classifier is robust to. -/
def robustnessRegion {X L : Type*} (c : Classifier X L) :
    Set (AdversarialAttack X) :=
  {a | ∀ x, robust_at c a x}



/-- Pointwise robustness: the set of points where classifier is robust to attack a. -/
def robustPoints {X L : Type*} (c : Classifier X L) (a : AdversarialAttack X) : Set X :=
  {x | robust_at c a x}


/-! ## Section 4: The Contrarian Attack Theorem -/

/-- The complementary (anti) binary classifier: flips all labels. -/
def antiClassifier {X : Type*} (c : Classifier X Bool) : Classifier X Bool where
  classify := fun x => !(c.classify x)




/-! ## Section 5: Attack Effects and Lattice Structure -/

/-- The attack effect: the set of inputs where classification changes. -/
def attackEffect {X L : Type*} (c : Classifier X L) (a : AdversarialAttack X) : Set X :=
  {x | c.classify (a.perturb x) ≠ c.classify x}

/-- An attack refines another if its effect is a subset. -/
def attackRefines {X L : Type*} (c : Classifier X L)
    (a₁ a₂ : AdversarialAttack X) : Prop :=
  attackEffect c a₁ ⊆ attackEffect c a₂



/-! ## Section 6: Perturbation Budgets and ε-Robustness -/

/-- ε-robustness: the classifier is robust to all attacks in the budget. -/
def epsilonRobust {X L : Type*} (c : Classifier X L)
    (budget : Set (AdversarialAttack X)) : Prop :=
  robust c budget



/-! ## Section 7: The Adversarial Information Theorem -/



/-! ## Section 8: Oracle-Attack Correspondence -/

/-- Convert a binary classifier to an oracle (set). -/
def classifierToOracle {X : Type*} (c : Classifier X Bool) : Set X :=
  {x | c.classify x = true}



/-! ## Section 9: Composition Theorems -/


/-! ## Section 10: Robustness Region is Downward-Closed -/




end


