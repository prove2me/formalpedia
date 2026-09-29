-- Prove2me | solution 1 for MaximumCliqueReductions.clique_extension_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:43:15.543141+00:00
-- url     : https://prove2.me/submissions/f3285fb2-a080-4d38-bbd6-3f807ab4e7a5

-- Sol generated from Applications/RamseyTheory/MaximumCliqueReductions.lean
import Mathlib
import Definitions.Def_Applications_RamseyTheory_MaximumCliqueReductions

/-!
# Upper-bound-driven reductions for maximum clique

This file isolates the mathematical core of upper-bound-enhanced core and truss
reductions. An upper-bound oracle is treated extensionally: on every vertex set
it bounds the cardinality of every finite clique contained there. The results
show that a clique can contain a proposed pattern only when the oracle value on
its common neighborhood is large enough, and that repeated certified vertex
peeling preserves every clique above the target size.
-/

open Set

open MaximumCliqueReductions

variable {V : Type*} (G : SimpleGraph V)













open MaximumCliqueReductions in
theorem solution{ub : Set V → ℕ} (hub : IsCliqueUpperBound G ub)
    {S C D : Set V} (hCfin : C.Finite) (hC : IsClique G C)
    (hD : D ⊆ C) (hCS : C ⊆ S) :
    C.ncard ≤ D.ncard + ub (S ∩ commonNeighbors G D) := by
  -- Let $E = C \setminus D$. Then $E$ is a finite clique in $S \cap \text{commonNeighbors } D$.
  set E := C \ D
  have hE_fin : E.Finite := by
    exact hCfin.subset fun x hx => hx.1
  have hE_clique : IsClique G E := by
    exact fun x hx y hy hxy => hC hx.1 hy.1 hxy
  have hE_subset : E ⊆ S ∩ commonNeighbors G D := by
    intro v hv; have := hCS hv.1; simp_all +decide [ commonNeighbors ] ;
    exact fun w hw => hC hv.1 ( hD hw ) ( by aesop );
  convert Nat.add_le_add_left ( hub ( S ∩ commonNeighbors G D ) E hE_fin hE_clique hE_subset ) D.ncard using 1;
  rw [ ← @Set.ncard_union_eq ];
  · rw [ Set.union_diff_cancel hD ];
  · exact disjoint_sdiff_self_right;
  · exact hCfin.subset hD;
  · exact hE_fin
