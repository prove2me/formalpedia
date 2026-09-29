-- Prove2me | solution 1 for bp_flt_for_p_ge_5
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-20T01:04:55.198389+00:00
-- url     : https://prove2.me/submissions/51db8094-4e05-46d5-8a87-5b1dc35c1b55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_bp_flt_for_p_ge_5
import Theorems.Thm_bp_frey_package_of_counterexample
import Theorems.Thm_bp_no_frey_package
import Definitions.Def_bp_FreyPackage

/-!
Sketch 2: reduce FLT for prime p ≥ 5 to the non-existence of a Frey package.

Blueprint chapter 2 §2.5–2.6: a counterexample a^p + b^p = c^p with p prime,
p ≥ 5 yields (after dividing by gcd, permuting, and possibly negating) a Frey
package — the bundle of arithmetic conditions that make the Frey curve
Y² = X(X − aᵖ)(X + bᵖ) suitable for the modularity argument. So FLT for p ≥ 5
follows from `bp_no_frey_package`.
-/

theorem solution (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) : a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
  have heq' : (a : ℤ) ^ p + (b : ℤ) ^ p = (c : ℤ) ^ p := by exact_mod_cast heq
  obtain ⟨P⟩ := bp_frey_package_of_counterexample a b c ha' hb' hc' p hp h5 heq'
  exact bp_no_frey_package P
