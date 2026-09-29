-- Prove2me | Definitions.Def_Probability_TropicalSocialChoiceEvidence
-- name    : Probability_TropicalSocialChoiceEvidence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:58.751641+00:00
-- url     : https://prove2.me/theorems/8de50b39-90e9-4c22-8439-66f5acd20c94
-- title:
--   Aether Catalog definitions — Probability_TropicalSocialChoiceEvidence
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TropicalSocialChoiceEvidence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TropicalSocialChoiceEvidence.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Executable small-case evidence for tropical social choice

This file makes the computational evidence for
`Probability.TropicalSocialChoice` and `Probability.TropicalSocialChoiceOligarchy`
kernel-checkable.  We work in the *integral* min-plus semiring `T = Option ℤ`
(`none = ∞ =` tropical zero, `some 0 =` tropical one, `⊕ = min`, `⊙ = +`), which is a
sub-semiring of `Tropical (WithTop ℝ)`, so every finite check below transfers verbatim.

A rule is presented by its coefficient list `a`, acting by `x ↦ ⨁ᵢ aᵢ ⊙ xᵢ`.

Kernel-checked results (all by `decide`):

* `paretoCount_two`, `paretoCount_three`, `paretoCount_four` : over the coefficient grid
  `{∞, 0, 1, 2}` the number of *unanimous* rules on `n = 2, 3, 4` voters is `7, 37, 175`,
  i.e. `4ⁿ − 3ⁿ`.
* `swfCount_two`, `swfCount_three`, `swfCount_four` : of these, the ones that are also
  tropically multiplicative number exactly `2`, `3` and `4` — the dictators, with none
  left over (`nondictatorialSWFCount_two`, `nondictatorialSWFCount_three`,
  `nondictatorialSWFCount_four`), confirming the tropical Arrow theorem in the finite
  window.
* `rawlsian_evidence` : the Rawlsian rule `a = (0,0)` is unanimous, non-multiplicative and
  non-dictatorial — the witness formalised as `exists_nondictatorial_of_tropPareto_tropIIA`.
* `rawlsian_diagIdem_evidence`, `weighted_not_diagIdem_evidence` : the Rawlsian rule *is*
  diagonally idempotent while the weighted rule `a = (0,1)` is not, matching the oligarchy
  classification `oligarchy_iff`.
* `oligarchyCount_two`, `oligarchyCount_three`, `oligarchyCount_four` : the unanimous,
  diagonally idempotent rules number `3`, `7` and `15`, i.e. `2ⁿ − 1` — the nonempty
  coalitions, as classified by `oligarchy_iff`.
-/

set_option maxRecDepth 100000

namespace TropicalSocialChoiceEvidence

/-- Extended integer costs: `none` is `∞` (the tropical zero). -/
abbrev T := Option ℤ

/-- Tropical addition: the better (smaller) of two costs. -/
def tadd : T → T → T
  | none, y => y
  | x, none => x
  | some a, some b => some (min a b)

/-- Tropical multiplication: ordinary addition of costs. -/
def tmul : T → T → T
  | none, _ => none
  | _, none => none
  | some a, some b => some (a + b)

/-- Tropical sum of a list of costs. -/
def tsum (l : List T) : T := l.foldl tadd none

/-- Pointwise tropical product of two profiles. -/
def profMul (x y : List T) : List T := List.zipWith tmul x y

/-- The tropical linear form with coefficient list `a`, evaluated at the profile `x`. -/
def form (a x : List T) : T := tsum (List.zipWith tmul a x)

/-- The coefficient grid `{∞, 0, 1, 2}`. -/
def coefGrid : List T := [none, some 0, some 1, some 2]

/-- The profile grid `{∞, 0, 1}` on which the axioms are tested. -/
def profGrid : List T := [none, some 0, some 1]

/-- All length-`n` lists with entries in `g`. -/
def vectors (g : List T) : ℕ → List (List T)
  | 0 => [[]]
  | n + 1 => (vectors g n).flatMap fun v => g.map fun c => c :: v

/-- Tropical Pareto (unanimity) for the coefficient list `a`: `⨁ᵢ aᵢ = 1`. -/
def paretoB (a : List T) : Bool := tsum a == some 0

/-- Tropical multiplicativity, tested on all profiles from `profGrid`. -/
def mulOK (n : ℕ) (a : List T) : Bool :=
  (vectors profGrid n).all fun x => (vectors profGrid n).all fun y =>
    form a (profMul x y) == tmul (form a x) (form a y)

/-- Diagonal idempotence `f (x ⊙ x) = f x ⊙ f x`, tested on all profiles from
`profGrid`. -/
def diagIdemOK (n : ℕ) (a : List T) : Bool :=
  (vectors profGrid n).all fun x =>
    form a (profMul x x) == tmul (form a x) (form a x)

/-- Being a dictator: exactly one coefficient is `0` and all others are `∞`. -/
def isDict (a : List T) : Bool :=
  (a.filter fun c => c == some (0 : ℤ)).length == 1 &&
    (a.all fun c => c == none || c == some (0 : ℤ))

/-- Number of unanimous rules on `n` voters over the coefficient grid. -/
def paretoCount (n : ℕ) : ℕ := ((vectors coefGrid n).filter paretoB).length

/-- Number of unanimous *and* tropically multiplicative rules on `n` voters. -/
def swfCount (n : ℕ) : ℕ :=
  ((vectors coefGrid n).filter fun a => paretoB a && mulOK n a).length

/-- Number of unanimous, multiplicative and *non-dictatorial* rules on `n` voters. -/
def nondictatorialSWFCount (n : ℕ) : ℕ :=
  ((vectors coefGrid n).filter fun a => paretoB a && mulOK n a && !isDict a).length

/-- Number of unanimous, diagonally idempotent rules on `n` voters. -/
def oligarchyCount (n : ℕ) : ℕ :=
  ((vectors coefGrid n).filter fun a => paretoB a && diagIdemOK n a).length

/-! ### Counts of unanimous rules: `4ⁿ − 3ⁿ` -/




/-! ### The tropical Arrow theorem in the finite window: only dictators survive -/







/-! ### The Rawlsian escape -/



/-! ### Diagonal idempotence separates coalition rules from weighted rules -/






end TropicalSocialChoiceEvidence


