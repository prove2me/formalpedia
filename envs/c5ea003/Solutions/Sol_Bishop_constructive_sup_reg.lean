-- Prove2me | solution 1 for Bishop.constructive_sup_reg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:34:13.101194+00:00
-- url     : https://prove2.me/submissions/adf66440-7c4e-460b-92df-ddc54de3b41a

-- Sol generated from Logic/ConstructiveAnalysis/ConstructiveSup.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveSup
import Theorems.Thm_Bishop_Reg_toReal_eq_of_approx_le
import Theorems.Thm_Bishop_constructive_sup
import Theorems.Thm_Bishop_exists_bisect_index
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
theorem solution{S : Set ℝ} (D : LocatedData S) {a₀ b₀ : ℚ} (hab : a₀ < b₀)
    (h₀ : Enclosing S (a₀, b₀)) :
    ∃ x : Reg, IsLUB S x.toReal ∧
      ∀ k : ℕ, ∃ n : ℕ, x.approx k = (bisect D.L a₀ b₀ n).1 := by
  obtain ⟨u, hu, henc⟩ := constructive_sup D hab h₀
  have hchoice : ∀ k : ℕ, ∃ n : ℕ, |(((bisect D.L a₀ b₀ n).1 : ℚ) : ℝ) - u| ≤ 1 / (k + 1) := by
    intro k
    obtain ⟨n, hn⟩ := exists_bisect_index a₀ b₀ hab k
    obtain ⟨h1, h2, h3⟩ := henc n
    refine ⟨n, ?_⟩
    rw [abs_le]
    constructor <;> [linarith; linarith]
  choose N hN using hchoice
  set q : ℕ → ℚ := fun k => (bisect D.L a₀ b₀ (N k)).1 with hq
  have hreg : ∀ m n : ℕ, |q m - q n| ≤ 1 / (m + 1) + 1 / (n + 1) := by
    intro m n
    have hR : |((q m : ℚ) : ℝ) - ((q n : ℚ) : ℝ)| ≤ 1 / (m + 1) + 1 / (n + 1) := by
      have h1 : |((q m : ℚ) : ℝ) - ((q n : ℚ) : ℝ)|
          ≤ |((q m : ℚ) : ℝ) - u| + |u - ((q n : ℚ) : ℝ)| := abs_sub_le _ _ _
      have h2 := hN m
      have h3 : |u - ((q n : ℚ) : ℝ)| ≤ 1 / (n + 1) := by
        rw [abs_sub_comm]; exact hN n
      linarith
    have h' : ((|q m - q n| : ℚ) : ℝ) ≤ (((1 : ℚ) / (m + 1) + 1 / (n + 1) : ℚ) : ℝ) := by
      push_cast
      simpa using hR
    exact_mod_cast h'
  have hx : (⟨q, hreg⟩ : Reg).toReal = u := by
    refine Reg.toReal_eq_of_approx_le _ u 1 (fun k => ?_)
    have happ : (⟨q, hreg⟩ : Reg).approx k = q k := rfl
    rw [happ, one_mul]
    exact hN k
  refine ⟨⟨q, hreg⟩, ?_, ?_⟩
  · rw [hx]; exact hu
  · intro k; exact ⟨N k, rfl⟩
