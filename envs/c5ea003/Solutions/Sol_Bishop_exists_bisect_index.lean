-- Prove2me | solution 1 for Bishop.exists_bisect_index
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:32:32.471611+00:00
-- url     : https://prove2.me/submissions/bcafdbac-4433-4497-854c-9866c365058a

-- Sol generated from Logic/ConstructiveAnalysis/ConstructiveSup.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveSup
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


open Bishop

open Set
















/-! ## A worked instance: the hypotheses are satisfiable

To see that `LocatedData` is not a vacuous requirement, here is a completely
explicit instance — a set whose locatedness oracle is a decidable comparison of
rationals — on which the trisection search really runs. -/



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



open Bishop in
theorem solution(a₀ b₀ : ℚ) (hab : a₀ < b₀) (k : ℕ) :
    ∃ n : ℕ, (2 / 3 : ℝ) ^ n * ((b₀ : ℝ) - (a₀ : ℝ)) ≤ 1 / (k + 1) := by
  have hW : (0 : ℝ) < (b₀ : ℝ) - (a₀ : ℝ) := by
    have : (a₀ : ℝ) < (b₀ : ℝ) := by exact_mod_cast hab
    linarith
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have h23 : |(2 / 3 : ℝ)| < 1 := by rw [abs_of_nonneg] <;> norm_num
  have htend : Filter.Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n * ((b₀ : ℝ) - (a₀ : ℝ)))
      Filter.atTop (nhds (0 * ((b₀ : ℝ) - (a₀ : ℝ)))) :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h23).mul_const _
  rw [zero_mul] at htend
  have := (htend.eventually (eventually_le_nhds hk)).exists
  obtain ⟨n, hn⟩ := this
  exact ⟨n, hn⟩
