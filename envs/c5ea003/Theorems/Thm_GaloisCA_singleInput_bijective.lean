-- Prove2me | Theorems.Thm_GaloisCA_singleInput_bijective
-- name    : GaloisCA.singleInput_bijective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:48:19.052816+00:00
-- url     : https://prove2.me/theorems/7186bf84-e38d-460b-aec4-7826c7b82b3e
-- title:
--   SingleInput bijective
-- statement:
--   Formal statement of `GaloisCA.singleInput_bijective` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem GaloisCA.singleInput_bijective{n : ℕ} (hn : 0 < n) (f : LocalRule)
--       (hf : isSingleInput f) :
--       Function.Bijective (globalMap f hn) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CellularAutomata/GaloisCellularAutomata.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CellularAutomata/GaloisCellularAutomata.lean#L339

-- Thm stub generated from Bridges/CellularAutomata/GaloisCellularAutomata.lean
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

/-
Right and left index operations are inverse: rightIdx ∘ leftIdx = id
-/







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

theorem GaloisCA.singleInput_bijective{n : ℕ} (hn : 0 < n) (f : LocalRule)
    (hf : isSingleInput f) :
    Function.Bijective (globalMap f hn) := by sorry
