-- Prove2me | solution 1 for Arexychen.Erdos180.matchingHost_isMatchingGraph
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:27:10.350968+00:00
-- url     : https://prove2.me/submissions/a9e11820-de9f-49c3-b220-3e2d39479b8d

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_matching
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w









end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180 in
/-- The labelled matching host is a matching graph. -/
theorem solution (n : ℕ) :
    IsMatchingGraph (matchingHost n) := by
  intro x y z hxy hxz
  rcases hxy with ⟨k, hxy | hxy⟩
  · rcases hxy with ⟨hxk, hyk⟩
    rcases hxz with ⟨l, hxz | hxz⟩
    · rcases hxz with ⟨hxl, hzl⟩
      subst y
      subst z
      have hkl : k = l := by
        apply Fin.ext
        have hv := congrArg Fin.val (hxk.symm.trans hxl)
        simp [matchingHostLeft] at hv
        omega
      subst l
      rfl
    · rcases hxz with ⟨hzl, hxl⟩
      have hbad := congrArg Fin.val (hxk.symm.trans hzl)
      simp [matchingHostLeft, matchingHostRight] at hbad
      omega
  · rcases hxy with ⟨hyk, hxk⟩
    rcases hxz with ⟨l, hxz | hxz⟩
    · rcases hxz with ⟨hxl, hzl⟩
      have hbad := congrArg Fin.val (hyk.symm.trans hxl)
      simp [matchingHostLeft, matchingHostRight] at hbad
      omega
    · rcases hxz with ⟨hzl, hxl⟩
      subst y
      subst z
      have hkl : k = l := by
        apply Fin.ext
        have hv := congrArg Fin.val (hyk.symm.trans hzl)
        simp [matchingHostRight] at hv
        omega
      subst l
      rfl
end
namespace Arexychen
noncomputable section
namespace Erdos180










end Erdos180

end
end Arexychen
