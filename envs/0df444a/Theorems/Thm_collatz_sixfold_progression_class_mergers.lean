-- Prove2me | Theorems.Thm_collatz_sixfold_progression_class_mergers
-- name    : collatz_sixfold_progression_class_mergers
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T19:46:38.601353+00:00
-- url     : https://prove2.me/theorems/43554ba4-2cfb-56fe-ba1d-8b499a162570
-- title:
--   Smaller Collatz mergers below the sixfold cap in seventeen congruence classes
-- statement:
--   Let $C$ be the ordinary Collatz map. Suppose $n$ belongs to at least one of the following congruence classes.
--
--   - $n\equiv 14335\pmod{69984}$
--   - $n\equiv 146527\pmod{629856}$
--   - $n\equiv 3995647\pmod{5668704}$
--   - $n\equiv 37378015\pmod{51018336}$
--   - $n\equiv 109181599\pmod{153055008}$
--   - $n\equiv 840444415\pmod{1377495072}$
--   - $n\equiv 3901544575\pmod{12397455648}$
--   - $n\equiv 6197369695\pmod{37192366944}$
--   - $n\equiv 208689145279\pmod{334731302496}$
--   - $n\equiv 2737770097471\pmod{3012581722464}$
--   - $n\equiv 1064113584991\pmod{27113235502176}$
--   - $n\equiv 74370268831615\pmod{81339706506528}$
--   - $n\equiv 472031056196863\pmod{732057358558752}$
--   - $n\equiv 2749542838379647\pmod{6588516227028768}$
--   - $n\equiv 6653848750692991\pmod{19765548681086304}$
--   - $n\equiv 169170582350735935\pmod{177889938129776736}$
--   - $n\equiv 307529423118340063\pmod{1601009443167990624}$
--
--   Prove that there is a smaller positive start with a common ordinary iterate.
--
--   The desired merger is
--   $$
--   \exists k,a,b\in\mathbb N,\qquad 0<k<n,\qquad C^a(n)=C^b(k).
--   $$
--
--   Also prove that the two starts are connected in the shortcut Collatz graph restricted to heights at most $6n+2$. The shortcut pairs each odd step with the halving that follows it.
-- source:
--   Sublemma of https://prove2.me/theorems/db9b60ec-72e1-5e71-adc2-467b3036fcef. The inverse relay and choice of rounds follow Sections 4 and 5 of https://rstation.ai/problems/collatz/papers/213.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

theorem collatz_sixfold_progression_class_mergers (n : ℕ)
    (h : ∃ a : ℕ × ℕ, a ∈
      ([(69984, 14335),
       (629856, 146527),
       (5668704, 3995647),
       (51018336, 37378015),
       (153055008, 109181599),
       (1377495072, 840444415),
       (12397455648, 3901544575),
       (37192366944, 6197369695),
       (334731302496, 208689145279),
       (3012581722464, 2737770097471),
       (27113235502176, 1064113584991),
       (81339706506528, 74370268831615),
       (732057358558752, 472031056196863),
       (6588516227028768, 2749542838379647),
       (19765548681086304, 6653848750692991),
       (177889938129776736, 169170582350735935),
       (1601009443167990624, 307529423118340063)] : List (ℕ × ℕ)) ∧ n%a.1=a.2) :
    let shortcut : ℕ → ℕ := fun x =>
      if x % 2 = 0 then x / 2 else (3*x+1)/2
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k ∧
      Relation.EqvGen (fun x y => x<6*n+3 ∧ y<6*n+3 ∧ shortcut x=y) n k := by
  sorry
