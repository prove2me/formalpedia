-- Prove2me | Definitions.Def_Probability_TropicalSocialChoice
-- name    : Probability_TropicalSocialChoice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:55.972251+00:00
-- url     : https://prove2.me/theorems/6de12c75-ff07-457e-b497-5a53e4f01499
-- title:
--   Aether Catalog definitions — Probability_TropicalSocialChoice
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TropicalSocialChoice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TropicalSocialChoice.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice: a min-plus Arrow theorem

We work in the tropical (min-plus) semiring `TR = Tropical (WithTop ℝ)` of *extended
costs*: tropical addition is `min` (the better of two costs), tropical multiplication is
ordinary addition of costs, the tropical `0` is `⊤` ("infinitely bad") and the tropical
`1` is the real number `0` ("neutral").

A *tropical social welfare function* on `n` voters is a map `f : TRⁿ → TR` subject to

* `IsTropLinear f` : `f x = ⨁ᵢ aᵢ ⊙ xᵢ` for some coefficient vector `a` (tropical
  linearity — this is the tropical analogue of *independence of irrelevant
  alternatives*: the aggregate is assembled coordinatewise, with no cross terms);
* `TropPareto f` : `f (c, …, c) = c` (unanimity / tropical Pareto);
* `TropScaleInv f` : `f (x ⊙ y) = f x ⊙ f y` (tropical multiplicativity: aggregating a
  sum of two cost profiles is the same as summing the two aggregates — the tropical
  analogue of *neutrality under a common change of scale*).

## Main results

* `tropical_arrow` : the three axioms force `f` to be the projection `x ↦ x k` for a
  unique voter `k` — a *tropical dictator*.
* `isTropLinear_of_tropIIA`, `tropical_arrow_of_tropIIA`, `tropical_arrow_tropIIA_iff` :
  linearity is in fact *derivable*, so the theorem holds with the weaker hypothesis
  `TropIIA` (preservation of tropical addition) in place of `IsTropLinear`.
* `tropForm_sandwich` : every unanimous tropical linear rule lies between the Rawlsian
  rule and the minimum rule of its oligarchy `{i | aᵢ = 1}`.
* `tropical_arrow_iff`, `tropicalSWF_eq_range_tropDictator` : the exact characterisation
  and the corresponding set equality; distinct voters give distinct dictators
  (`tropDictator_injective`).
* `exists_nondictatorial_of_tropPareto_tropIIA` : dropping only tropical
  multiplicativity, the "Rawlsian" rule `x ↦ ⨁ᵢ xᵢ` (the minimum cost, i.e. maximin) is
  tropically linear, satisfies tropical IIA and tropical Pareto, and is *not*
  dictatorial.  This confirms the conjecture that the weaker tropical axiom system
  admits non-dictatorial rules.
* `softMin_tendsto_inf'`, `trop_inf'_eq_tropCoalition` : the classical (zero
  temperature, Maslov dequantisation) limit.  The Boltzmann aggregator
  `-(1/t) log ∑ᵢ exp (-t yᵢ)` converges as `t → ∞` to the tropical coalition rule, and
  the tropical rule is literally the tropicalisation of that limit.
* `arrow_classical_dictatorship` : the *ordinal* rule induced by a tropical social
  welfare function ranks alternatives exactly as voter `k` does — Arrow's conclusion.
  The induced rule of a dictator satisfies classical Pareto and classical IIA
  (`dictator_classical_IIA`), while the non-dictatorial Rawlsian rule violates
  classical IIA (`rawlsian_violates_classical_IIA`), which is precisely why it escapes
  Arrow's theorem.
-/

namespace TropicalSocialChoice

open Finset Filter Tropical

/-- The tropical semiring of extended real costs: `⊕ = min`, `⊙ = +`,
tropical zero `= ⊤`, tropical one `= (0 : ℝ)`. -/
abbrev TR := Tropical (WithTop ℝ)

/-- A real number viewed as a (finite) tropical cost. -/
noncomputable def ofReal (r : ℝ) : TR := trop ((r : ℝ) : WithTop ℝ)



/-! ## The axioms -/

section Axioms

variable {n : ℕ}

/-- The tropical linear form with coefficient vector `a` : `x ↦ ⨁ᵢ aᵢ ⊙ xᵢ`, i.e.
`x ↦ minᵢ (aᵢ + xᵢ)`. -/
noncomputable def tropForm (a x : Fin n → TR) : TR := ∑ i, a i * x i

/-- `f` is a tropical linear map, i.e. a tropical `1 × n` matrix.  This is the tropical
form of independence of irrelevant alternatives: the social cost is assembled from the
individual costs coordinatewise, with no interaction terms. -/
def IsTropLinear (f : (Fin n → TR) → TR) : Prop := ∃ a : Fin n → TR, ∀ x, f x = tropForm a x

/-- Tropical Pareto (unanimity): if everybody assigns cost `c`, so does society. -/
def TropPareto (f : (Fin n → TR) → TR) : Prop := ∀ c : TR, f (fun _ => c) = c

/-- Tropical IIA: `f` preserves tropical addition, i.e. commutes with taking the
coordinatewise better of two profiles. -/
def TropIIA (f : (Fin n → TR) → TR) : Prop := ∀ x y, f (x + y) = f x + f y

/-- Tropical scale invariance: `f` preserves tropical multiplication, i.e. commutes with
adding two cost profiles. -/
def TropScaleInv (f : (Fin n → TR) → TR) : Prop := ∀ x y, f (x * y) = f x * f y

/-- The tropical dictator: society copies voter `k`. -/
def tropDictator (k : Fin n) : (Fin n → TR) → TR := fun x => x k

/-- `f` is dictatorial. -/
def IsTropDictatorial (f : (Fin n → TR) → TR) : Prop := ∃ k, f = tropDictator k

/-! ### Basic properties of tropical linear forms -/











/-! ### Tropical linearity is *derivable* from the other two axioms -/





/-! ### The dictator satisfies every axiom -/







/-! ## The tropical Arrow theorem -/







end Axioms

/-! ## Escaping the theorem: coalition (Rawlsian) rules -/

section Coalition

variable {n : ℕ}

/-- The coalition rule of a set `s` of voters: the social cost is the tropical sum
(= minimum) of the costs of the members of `s`.  For `s = univ` this is the Rawlsian
maximin rule. -/
noncomputable def tropCoalition (s : Finset (Fin n)) : (Fin n → TR) → TR := fun x => ∑ i ∈ s, x i







/-- The oligarchy of a coefficient vector: the voters whose coefficient is `1`, i.e. who
enter the aggregate with no handicap. -/
noncomputable def tropSupport (a : Fin n → TR) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a i = 1)







end Coalition

/-! ## The classical limit: Maslov dequantisation -/

section ClassicalLimit

variable {ι : Type*}

/-- The Boltzmann ("finite temperature") aggregator at inverse temperature `t`:
`-(1/t) · log ∑ᵢ exp (-t yᵢ)`.  It is a smooth, strictly Paretian aggregator of real
costs. -/
noncomputable def softMin (s : Finset ι) (t : ℝ) (y : ι → ℝ) : ℝ :=
  -(1 / t) * Real.log (∑ i ∈ s, Real.exp (-(t * y i)))





end ClassicalLimit

/-! ## Reduction to classical (ordinal) social choice -/

section Classical

variable {n : ℕ} {α : Type*}

/-- The social cost that a tropical rule `f` assigns to alternative `a`, given a profile
`u` of individual cost functions (lower cost = more preferred). -/
noncomputable def socialCost (f : (Fin n → TR) → TR) (u : Fin n → α → ℝ) (a : α) : TR :=
  f (fun i => ofReal (u i a))

/-- The induced ordinal social preference: society weakly prefers `a` to `b`. -/
def SocPrefers (f : (Fin n → TR) → TR) (u : Fin n → α → ℝ) (a b : α) : Prop :=
  socialCost f u a ≤ socialCost f u b






end Classical

end TropicalSocialChoice


