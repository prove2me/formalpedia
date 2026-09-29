-- Prove2me | solution 1 for MonsterMoonshineBridge.fixedPointCoefficient_conj_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:41:19.014548+00:00
-- url     : https://prove2.me/submissions/db3a450f-ba69-43f8-b4b6-2bb9be3fb822

-- Sol generated from Novelty/MonsterMoonshineBridge.lean
import Mathlib
import Definitions.Def_Novelty_MonsterMoonshineBridge

/-!
# A coefficientwise bridge from group characters to moonshine series

The proposed product of all McKay--Thompson series is not presently a theorem, and in its
literal form it has basic normalization problems (recorded in `FUTURE_DIRECTIONS.md`).  This
file instead proves a rigorous bridge fundamental to the interpretation of moonshine
coefficients.

A graded finite `G`-set `X n` has a fixed-point (permutation-character) series for every
`g : G`.  The coefficientwise average of these series is exactly the orbit-counting series.
Thus a family of character-like q-expansions determines an enumerative generating function.
This is Burnside's lemma lifted, simultaneously in every grade, to formal q-series represented
by their coefficient functions.
-/

open MonsterMoonshineBridge


variable (G : Type*) [Group G]
variable (X : ℕ → Type*) [∀ n, MulAction G (X n)]


variable [∀ n (g : G), Fintype (MulAction.fixedBy (X n) g)]




variable [Fintype G]
variable [∀ n, Fintype (MulAction.orbitRel.Quotient G (X n))]











open MonsterMoonshineBridge in
theorem solution(g h : G) (n : ℕ) :
    fixedPointCoefficient G X (h * g * h⁻¹) n = fixedPointCoefficient G X g n := by
  let e : MulAction.fixedBy (X n) g ≃ MulAction.fixedBy (X n) (h * g * h⁻¹) :=
    { toFun := fun x => ⟨h • x, by
        rw [MulAction.mem_fixedBy]
        rw [mul_smul, mul_smul, inv_smul_smul]
        exact congrArg (fun y => h • y) (MulAction.mem_fixedBy.mp x.property)⟩
      invFun := fun x => ⟨h⁻¹ • x, by
        rw [MulAction.mem_fixedBy]
        have hx := MulAction.mem_fixedBy.mp x.property
        calc
          g • (h⁻¹ • x.1) = h⁻¹ • ((h * g * h⁻¹) • x.1) := by simp [mul_smul]
          _ = h⁻¹ • x.1 := congrArg (fun y => h⁻¹ • y) hx⟩
      left_inv := fun x => by ext; simp
      right_inv := fun x => by ext; simp }
  exact (Fintype.card_congr e).symm
