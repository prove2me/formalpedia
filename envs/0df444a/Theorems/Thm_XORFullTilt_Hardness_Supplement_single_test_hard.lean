-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_Supplement_single_test_hard
-- name    : XORFullTilt.Hardness.Supplement.single_test_hard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:28:40.068485+00:00
-- url     : https://prove2.me/theorems/026382d8-4862-478a-84d7-dc3a5d466c7e
-- title:
--   Theorem 6.1 — RE-hardness with one supported non-XOR pair
-- statement:
--   There are fixed real constants $c>s$ such that every recursively enumerable language $L$ of finite binary strings admits a total computable map $r$ to explicitly encoded tilted games with
--   $$x\in L\Longrightarrow\omega^*(T(G_{r(x)}))\ge c,\qquad x\notin L\Longrightarrow\omega^*(T(G_{r(x)}))<s.$$
--   Here $T$ is the source's half-XOR, half-single-test construction: its only supported non-XOR pair tests whether Alice outputs zero on the same distinguished label used in the XOR component, while Bob receives a fresh dummy question and his answer is ignored. The constants are uniform over $L$ and its inputs. This supplies hardness even for this concrete output family.
--
--   Differences from the source:
--   - encoding: an XOR game with one additional zero-answer test, as constructed in the proof → the explicit half-and-half family T(G_n), with a fresh Bob label and the original Alice bottom label; reason: this is exactly the construction on pp.30–31; it makes the output game effective and retains the shared tested observable, rather than assuming the reduction properties in a structure
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p. 30, Theorem 6.1

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_Supplement_SingleTest

open Matrix Kronecker

namespace XORFullTilt.Hardness.Supplement

/-- Theorem 6.1, with the concrete half-and-half target family of its proof.
    No completeness or soundness property is assumed in singleTestGame. -/
theorem single_test_hard :
    ∃ c s : ℝ, s < c ∧
      ∀ L : List Bool → Prop, REPred L →
        ∃ r : List Bool → ℕ, Computable r ∧
          (∀ x, L x → singleTestValue (r x) ≥ c) ∧
          (∀ x, ¬ L x → singleTestValue (r x) < s) := by sorry
end XORFullTilt.Hardness.Supplement
