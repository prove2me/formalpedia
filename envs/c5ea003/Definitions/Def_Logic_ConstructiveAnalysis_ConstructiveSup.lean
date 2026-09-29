-- Prove2me | Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveSup
-- name    : Logic_ConstructiveAnalysis_ConstructiveSup
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:52:42.067475+00:00
-- url     : https://prove2.me/theorems/63ad1051-94dc-4630-8660-7e485f4b7c9a
-- title:
--   Aether Catalog definitions — Logic_ConstructiveAnalysis_ConstructiveSup
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ConstructiveAnalysis.ConstructiveSup`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ConstructiveAnalysis/ConstructiveSup.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
/-
# Bishop's constructive least upper bound principle

Classically every nonempty set of reals that is bounded above has a supremum.  That
proof is not constructive: it decides, for a rational `q`, whether `q` is an upper
bound of the set, which is in general undecidable.  Bishop's replacement assumes
that the set is **located**: it comes equipped with a *decision procedure* `L` such
that for rationals `p < q`, `L p q = true` guarantees that `q` is an upper bound,
and `L p q = false` produces a member of the set above `p`.  (Both alternatives may
hold; only their disjunction is asserted, which is what makes the datum obtainable
in practice.)

From such a datum the supremum is computed by an explicit **trisection search**
(`Bishop.bisect`), producing at every stage a pair of rationals `p n ≤ sup ≤ q n`
whose width is exactly `(2/3)^n (b₀ - a₀)`:

* `Bishop.bisect_width` : the exact geometric rate;
* `Bishop.bisect_invariant` : the enclosure invariant, proved by induction;
* `Bishop.constructive_sup` : the supremum exists, is the least upper bound, and is
  enclosed by the explicitly computed rationals with the stated rate;
* `Bishop.constructive_sup_reg` : the supremum, presented as a Bishop real, i.e. as a
  regular sequence of rationals with the canonical modulus `1/(n+1)`.

The located hypothesis is exactly what the classical proof hides: `Bishop.
locatedData_of_decidable` shows that assuming the classically valid but
constructively unavailable decision "is `q` an upper bound?" one recovers a located
datum, so the principle is classically equivalent to the ordinary completeness
axiom.
-/


namespace Bishop

open Set

/-- One step of the trisection search for the supremum of a located set: query the
locatedness oracle at the two interior trisection points, and keep the half-open
enclosure it certifies.  The width shrinks by the factor `2/3` in both branches. -/
def bisectStep (L : ℚ → ℚ → Bool) (pq : ℚ × ℚ) : ℚ × ℚ :=
  let p := pq.1
  let q := pq.2
  let m₁ := p + (q - p) / 3
  let m₂ := p + 2 * (q - p) / 3
  if L m₁ m₂ then (p, m₂) else (m₁, q)

/-- The trisection sequence of rational enclosures of the supremum. -/
def bisect (L : ℚ → ℚ → Bool) (a₀ b₀ : ℚ) : ℕ → ℚ × ℚ
  | 0 => (a₀, b₀)
  | n + 1 => bisectStep L (bisect L a₀ b₀ n)






/-- The invariant maintained by the search: the right endpoint is an upper bound of
`S`, and some member of `S` lies strictly above the left endpoint. -/
def Enclosing (S : Set ℝ) (pq : ℚ × ℚ) : Prop :=
  (∀ s ∈ S, s ≤ (pq.2 : ℝ)) ∧ ∃ s ∈ S, (pq.1 : ℝ) < s

/-- **Located set (Bishop).**  A decision procedure which, for rationals `p < q`,
either certifies that `q` is an upper bound of `S`, or exhibits a member of `S`
above `p`. -/
structure LocatedData (S : Set ℝ) where
  /-- the decision procedure. -/
  L : ℚ → ℚ → Bool
  /-- a `true` answer certifies an upper bound. -/
  upper : ∀ p q : ℚ, p < q → L p q = true → ∀ s ∈ S, s ≤ (q : ℝ)
  /-- a `false` answer produces a member of `S` above `p`. -/
  witness : ∀ p q : ℚ, p < q → L p q = false → ∃ s ∈ S, (p : ℝ) < s







/-! ## A worked instance: the hypotheses are satisfiable

To see that `LocatedData` is not a vacuous requirement, here is a completely
explicit instance — a set whose locatedness oracle is a decidable comparison of
rationals — on which the trisection search really runs. -/

/-- The located datum for the half-line `(-∞, c]` with rational endpoint `c`: the
oracle is the decidable rational test `c ≤ q`. -/
def locatedIic (c : ℚ) : LocatedData (Set.Iic (c : ℝ)) where
  L := fun _ q => decide (c ≤ q)
  upper := by
    intro p q _ h s hs
    have hcq : c ≤ q := of_decide_eq_true h
    have : (c : ℝ) ≤ (q : ℝ) := by exact_mod_cast hcq
    exact le_trans hs this
  witness := by
    intro p q hpq h
    have hcq : ¬ c ≤ q := of_decide_eq_false h
    have hqc : q < c := lt_of_not_ge hcq
    refine ⟨(c : ℝ), Set.mem_Iic.mpr (le_refl _), ?_⟩
    have : p < c := lt_trans hpq hqc
    exact_mod_cast this


/-! The search is genuinely computable; the following facts about the trisection for
`c = 1/2` on `[0,1]` are checked at compile time. -/

-- the first four enclosures
#guard (List.range 4).map (fun n => bisect (locatedIic (1/2)).L 0 1 n)
    = [(0, 1), (0, 2 / 3), (2 / 9, 2 / 3), (2 / 9, 14 / 27)]

-- after ten steps the width is exactly `(2/3)^10`
#guard (bisect (locatedIic (1/2)).L 0 1 10).2 - (bisect (locatedIic (1/2)).L 0 1 10).1
    = (2 / 3 : ℚ) ^ 10

-- and the enclosure does contain `1/2`
#guard (bisect (locatedIic (1/2)).L 0 1 10).1 < (1 / 2 : ℚ) &&
    (1 / 2 : ℚ) ≤ (bisect (locatedIic (1/2)).L 0 1 10).2


end Bishop


