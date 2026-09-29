-- Prove2me | solution 1 for ToricCode.qubit_X_degree_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:55:24.595231+00:00
-- url     : https://prove2.me/submissions/2ee13fc1-771c-420c-89df-6472002dc47c

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
theorem solution(e : Edge M N) : (xChecks M N e).card = 2 := by
  classical
  obtain ⟨b, u⟩ := e
  have hs := step_ne_zero M N hM hN (!b)
  have hne : ¬ (u = u - step M N (!b)) := fun hc => hs (by linear_combination hc)
  have hmap : xChecks M N (b, u)
      = Finset.univ.image (fun s : Bool => (if s then u - step M N (!b) else u : Face M N)) := by
    ext f
    simp only [xChecks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [d2_ne_zero_iff M N hM hN]
    constructor
    · rintro (h | h)
      · exact ⟨false, by simp [h]⟩
      · refine ⟨true, ?_⟩
        show u - step M N (!b) = f
        rw [h]
        ring
    · rintro ⟨s, hsv⟩
      cases s
      · left; simpa using hsv
      · right
        have hsv' : u - step M N (!b) = f := hsv
        rw [← hsv']
        ring
  rw [hmap, Finset.card_image_of_injective _ ?inj, Finset.card_univ]
  · simp
  case inj =>
    intro s1 s2 h
    cases s1 <;> cases s2
    · rfl
    · exact absurd (by simpa using h) hne
    · exact absurd (by simpa using h.symm) hne
    · rfl
