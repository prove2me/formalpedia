-- Prove2me | solution 1 for CliqueComplexFlag.flag_eq_cliqueComplex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:53:01.510342+00:00
-- url     : https://prove2.me/submissions/c6c57292-eb88-4fee-b8b3-7d151c854aa2

import Mathlib
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
open Classical CliqueComplexFlag in
theorem solution {V : Type*} {K : ASC V} (hflag : IsFlag K)
    (hsing : ∀ v : V, ({v} : Finset V) ∈ K.faces) :
    K = cliqueComplex (oneSkeleton K) := by
  obtain ⟨F, hF⟩ := K
  unfold cliqueComplex
  congr 1
  ext s
  constructor
  · -- a face is a clique of its one-skeleton: every pair inside it is a face
    intro hs u hu v hv huv
    refine ⟨huv, hF ?_ hs⟩
    exact Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩
  · -- a clique is a face, by the flag property
    intro hs
    exact hflag s (fun u _ => hsing u) (fun u hu v hv huv => (hs hu hv huv).2)
