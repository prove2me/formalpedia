-- Prove2me | Theorems.Thm_ZerothLawThermo_exists_partition_of_equivalence
-- name    : ZerothLawThermo.exists_partition_of_equivalence
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:44.267566+00:00
-- url     : https://prove2.me/theorems/fac87ea2-d728-4c07-9416-85e509ec1d01
-- title:
--   Thermal equilibrium partitions the systems into classes of mutual equilibrium
-- statement:
--   Let $S$ be a type of thermodynamic systems and suppose thermal equilibrium $\mathrm{TE}$ is an equivalence relation on $S$. Then there is a family $\mathcal P$ of subsets of $S$ such that
--
--   1. $\mathcal P$ is a partition of $S$: no member of $\mathcal P$ is empty, and every system $A\in S$ belongs to exactly one member of $\mathcal P$;
--   2. for all systems $A,B$,
--   $$\mathrm{TE}(A,B)\iff \exists\, c\in\mathcal P,\ A\in c\ \text{and}\ B\in c.$$
--
--   In words: systems split into disjoint classes; two systems are in thermal equilibrium exactly when they lie in the same class.
-- source:
--   Wikipedia, "Zeroth law of thermodynamics", revision oldid=1328026962, https://en.wikipedia.org/w/index.php?title=Zeroth_law_of_thermodynamics&oldid=1328026962; Section "Equivalence relation": "In other words, the set of all systems each in its own state of internal thermodynamic equilibrium may be divided into subsets in which every system belongs to one and only one subset, and is in thermal equilibrium with every other member of that subset, and is not in thermal equilibrium with a member of any other subset." Also section "Foundation of temperature", first paragraph after the list.

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem ZerothLawThermo.exists_partition_of_equivalence {S : Type*} (TE : S → S → Prop)
    (hTE : Equivalence TE) :
    ∃ P : Set (Set S), Setoid.IsPartition P ∧
      ∀ A B : S, TE A B ↔ ∃ c ∈ P, A ∈ c ∧ B ∈ c := by sorry
