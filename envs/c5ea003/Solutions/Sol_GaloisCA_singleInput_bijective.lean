-- Prove2me | solution 1 for GaloisCA.singleInput_bijective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:41:22.027547+00:00
-- url     : https://prove2.me/submissions/899983b1-9dc2-4fb5-9bfb-c44d520c4ec3

-- Sol generated from Bridges/CellularAutomata/GaloisCellularAutomata.lean
import Mathlib
import Definitions.Def_Bridges_CellularAutomata_GaloisCellularAutomata

/-!
# Galois Theory of Cellular Automata: Reversible Dynamics

We formalize the group structure of reversible elementary cellular automata
(ECAs) on periodic binary configurations. An elementary CA has radius 1 and
binary alphabet {0,1}, giving 256 possible local rules (Wolfram numbering).

## Main Results

* `globalMap_rule204_eq_id` — Rule 204 implements the identity map
* `globalMap_rule170_bijective` — Rule 170 (left shift) is bijective
* `globalMap_rule051_bijective` — Rule 51 (complement) is bijective
* `globalMap_rule000_not_injective` — Rule 0 is not injective for n ≥ 2
* `reversible_eca_periodic` — Every config under a reversible CA is periodic
* `shift_complement_comm` — Shift and complement commute as global maps

## Novel Definitions

* `CADynamicalSystem` — A CA viewed as a discrete dynamical system with orbit structure
* `ReversibilityIndex` — Measures how far a rule is from being reversible
-/

open GaloisCA

/-! ## Configuration Space and Local Rules -/



/-! ## Cyclic Index Operations on Fin n -/



/-! ## Global Map -/


/-! ## Named Elementary CA Rules (Wolfram Numbering)

The 6 reversible elementary CAs are exactly the rules whose output depends
on a single input variable, composed with an optional negation:
- Center-dependent: Rule 204 (c), Rule 51 (¬c)
- Right-dependent: Rule 170 (r), Rule 85 (¬r)
- Left-dependent: Rule 240 (l), Rule 15 (¬l)
-/








/-! ## Novel Definition: CA Dynamical System -/





/-! ## Novel Definition: Reversibility Index -/


/-! ## Cyclic Index Lemmas -/

/-
Left and right index operations are inverse: leftIdx ∘ rightIdx = id
-/
theorem leftIdx_rightIdx {n : ℕ} (hn : 0 < n) (i : Fin n) :
    leftIdx hn (rightIdx hn i) = i := by
  -- By definition of `leftIdx` and `rightIdx`, we have `leftIdx hn (rightIdx hn i) = i`.
  apply Fin.ext
  simp [leftIdx, rightIdx];
  rcases n with ( _ | _ | n ) <;> norm_num at *;
  simp +arith +decide [ Nat.mod_eq_of_lt ];
  norm_num [ ( by ring : n + i + 2 = n + 2 + i ) ];
  exact Fin.is_le i

/-
Right and left index operations are inverse: rightIdx ∘ leftIdx = id
-/
theorem rightIdx_leftIdx {n : ℕ} (hn : 0 < n) (i : Fin n) :
    rightIdx hn (leftIdx hn i) = i := by
  rcases n with ( _ | _ | n ) <;> norm_num [ Fin.ext_iff, leftIdx, rightIdx ] at *;
  · contradiction;
  · norm_num [ add_assoc, Nat.mod_eq_of_lt ]







/-! ## Rule Characterizations -/





/-! ## Bijection Proofs for Reversible Rules -/

/-
Rule 170 (left shift) is bijective
-/

/-
Rule 240 (right shift) is bijective
-/

/-
Rule 51 (complement) is an involution
-/


/-
Rule 170 and Rule 240 are inverses
-/

/-
Rule 240 and Rule 170 are inverses
-/

/-! ## Non-Reversibility of Rule 0 -/


/-
Rule 0 is not injective for n ≥ 1 (since all configs map to the same thing)
-/

/-! ## Commutativity: Shift and Complement Commute -/



/-
Complement is an involution
-/

/-
Left shift and complement commute as operations on configurations
-/

/-! ## Periodicity under Reversible CAs -/

/-
Every configuration under a bijective map on a finite type is periodic.
    This is a fundamental consequence of the pigeonhole principle:
    the orbit {s, f(s), f²(s), ...} in a finite set must eventually repeat.
-/

/-! ## Reversibility Index Properties -/

/-
The reversibility index of a bijective map is 0
-/

/-
The reversibility index of a constant map on a space with ≥ 2 elements is positive
-/

/-! ## Structure Theorem: Reversible ECA Classification -/


/-
Every single-input rule with a bijective function gives a bijective global map
-/

/-! ## Conjecture: Universal Reversibility Classification -/





open GaloisCA in
theorem solution{n : ℕ} (hn : 0 < n) (f : LocalRule)
    (hf : isSingleInput f) :
    Function.Bijective (globalMap f hn) := by
  rcases hf with ( ⟨ g, hg, hg' ⟩ | ⟨ g, hg, hg' ⟩ | ⟨ g, hg, hg' ⟩ );
  · -- In this case, the global map is � (�fun s => g ∘ s ∘ leftIdx hn).
    have h_global_map : globalMap f hn = fun s => g ∘ s ∘ leftIdx hn := by
      ext s i; simp +decide [ hg', globalMap ] ;
    simp_all +decide [ Function.Bijective ];
    constructor;
    · intro s t h_eq;
      ext i; have := congr_fun h_eq ( rightIdx hn i ) ; simp_all +decide [ Function.comp ] ;
      simp_all +decide [ leftIdx_rightIdx ];
      cases h : s i <;> cases h' : t i <;> aesop;
    · intro s; use fun i => g.invFun ( s ( rightIdx hn i ) ) ; ext i; simp +decide [ hg.2, Function.invFun_eq ( hg.2 _ ) ] ;
      rw [ rightIdx_leftIdx ];
  · have h_global : globalMap f hn = fun s => g ∘ s := by
      ext s i; simp +decide [ hg', globalMap ] ;
    rw [ h_global ];
    exact ⟨ fun s t h => funext fun i => hg.injective <| congr_fun h i, fun s => ⟨ fun i => hg.surjective ( s i ) |> Classical.choose, funext fun i => hg.surjective ( s i ) |> Classical.choose_spec ⟩ ⟩;
  · -- Since $g$ is bijective, the map $s \mapsto g \circ s \circ rightIdx$ is also bijective.
    have h_bijective : Function.Bijective (fun s : Fin n → Bool => g ∘ s ∘ rightIdx hn) := by
      constructor;
      · intro s t h_eq;
        simp_all +decide [ funext_iff, Function.Injective.eq_iff hg.injective ];
        intro x; specialize h_eq ( leftIdx hn x ) ; simp_all +decide [ rightIdx_leftIdx ] ;
      · intro t;
        cases' hg with hg₁ hg₂;
        choose f hf using hg₂;
        exact ⟨ fun i => f ( t ( leftIdx hn i ) ), funext fun i => by simp +decide [ hf, leftIdx_rightIdx hn i ] ⟩;
    convert h_bijective using 1;
    ext s i; simp +decide [ hg', globalMap ] ;
