-- Prove2me | solution 1 for ToricCode.face_size_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:43:39.589906+00:00
-- url     : https://prove2.me/submissions/cc096677-c98a-4152-87a3-9ed27e8bbd34

-- Sol generated from Geometry/ToricCode/Locality.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Locality
import Theorems.Thm_ToricCode_d2_ne_zero_iff
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
theorem solution(f : Face M N) : (xSupport M N f).card = 4 := by
  classical
  have hs := step_ne_zero M N hM hN
  have hmap : xSupport M N f = Finset.univ.image
      (fun bs : Bool × Bool =>
        ((bs.1, f + (if bs.2 then step M N (!bs.1) else 0)) : Edge M N)) := by
    ext e
    obtain ⟨b, u⟩ := e
    simp only [xSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Prod.exists, Prod.mk.injEq]
    rw [d2_ne_zero_iff M N hM hN]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨b, false, rfl, by simp⟩
      · exact ⟨b, true, rfl, by simp⟩
    · rintro ⟨b2, s, rfl, hu⟩
      cases s
      · left; simpa using hu.symm
      · right; simpa using hu.symm
  rw [hmap, Finset.card_image_of_injective _ ?inj, Finset.card_univ]
  · simp
  case inj =>
    rintro ⟨b1, s1⟩ ⟨b2, s2⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, hu⟩ := h
    have h3 : (if s1 then step M N (!b1) else 0) = (if s2 then step M N (!b1) else 0) := by
      linear_combination hu
    cases s1 <;> cases s2
    · rfl
    · exact absurd (by simpa using h3.symm) (hs (!b1))
    · exact absurd (by simpa using h3) (hs (!b1))
    · rfl
