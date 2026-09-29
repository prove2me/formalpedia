-- Prove2me | solution 1 for ToricCode.d1_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:41:55.092519+00:00
-- url     : https://prove2.me/submissions/6c863608-8781-4f08-b322-241133f6ea2f

-- Sol generated from Geometry/ToricCode/Locality.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Locality
/-!
# Bounded local geometry of the square torus cellulation

The previous research cycle explicitly flagged that its counterexamples were
*not* claimed to come from bounded-degree local cellulations, and listed
"bounded face size and bounded vertex degree" as a missing ingredient.  This
file supplies exactly that data for the square torus, for every `M, N ≥ 2`:

* `vertex_degree_eq_four` : every `Z`-stabilizer (vertex) acts on exactly `4`
  qubits;
* `face_size_eq_four` : every `X`-stabilizer (face) acts on exactly `4` qubits;
* `qubit_Z_degree_eq_two` and `qubit_X_degree_eq_two` : every qubit is touched
  by exactly `2` checks of each type.

Hence the toric code is an LDPC code with all check weights and qubit degrees
bounded by `4`, uniformly in `M` and `N`.  Combined with `ToricCode.Distance` this makes
the family a genuine geometric witness: bounded local geometry, fixed genus one,
and unbounded distance.
-/

open Matrix

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]


variable (hM : 2 ≤ M) (hN : 2 ≤ N)

include hM hN

omit [NeZero M] [NeZero N] in
lemma step_ne_zero (b : Bool) : step M N b ≠ 0 := by
  haveI : Fact (1 < M) := ⟨hM⟩
  haveI : Fact (1 < N) := ⟨hN⟩
  haveI := ZMod.nontrivial M
  haveI := ZMod.nontrivial N
  intro h
  cases b
  · exact one_ne_zero (congrArg Prod.fst h)
  · exact one_ne_zero (congrArg Prod.snd h)



/-! ### Check weights -/





/-! ### Qubit degrees -/








open ToricCode in
omit [NeZero M] [NeZero N] in
theorem solution(v : Vert M N) (b : Bool) (u : ZMod M × ZMod N) :
    d1 M N v (b, u) ≠ 0 ↔ (u = v ∨ u = v - step M N b) := by
  have hs := step_ne_zero M N hM hN b
  constructor
  · intro h
    by_cases h1 : v = u
    · exact Or.inl h1.symm
    · by_cases h2 : v = u + step M N b
      · right; rw [h2]; ring
      · exact absurd (by simp [d1, h1, h2]) h
  · rintro (rfl | rfl)
    · have hne : ¬ (u = u + step M N b) := fun hc => hs (by linear_combination -hc)
      simp only [d1, if_neg hne]
      decide
    · have hne : ¬ (v = v - step M N b) := fun hc => hs (by linear_combination hc)
      have hb : v - step M N b + step M N b = v := by ring
      simp only [d1, if_neg hne, hb]
      decide
